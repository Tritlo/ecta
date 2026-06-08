{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.ECTA.Internal.ECTA.Enumeration (
    TermFragment (..),
    termFragToTruncatedTerm,
    SuspendedConstraint (..),
    scGetPathTrie,
    scGetUVar,
    descendScs,
    UVarValue (..),
    EnumerationState (..),
    uvarCounter,
    uvarRepresentative,
    uvarValues,
    pruneDeps,
    initEnumerationState,
    EnumerateM,
    getUVarRepresentative,
    assimilateUvarVal,
    mergeNodeIntoUVarVal,
    getUVarValue,
    getTermFragForUVar,
    runEnumerateM,
    getPruneDepsOf,
    getPruneDeps,
    addPruneDep,
    deletePruneDep,
    fragRepresents,
    enumerateNode,
    enumerateEdge,
    firstExpandableUVar,
    enumerateOutUVar,
    enumerateOutFirstExpandableUVar,
    enumerateFully,
    expandTermFrag,
    expandPartialTermFrag,
    expandUVar,
    getAllTruncatedTerms,
    getAllTerms,
    getAllTermsPrune,
    enumPrune,
    naiveDenotation,
    naiveDenotationBounded,
) where

import Control.Monad (filterM, forM_, guard)
import Control.Monad.Identity (Identity)
import Control.Monad.State.Strict (StateT (..))
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe, isJust)
import Data.Monoid (Any (..))
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence

import Control.Lens (Lens', ix, lens, use, (%=), (.=))
import Control.Lens.TH (makeLensesFor)
import Pipes
import qualified Pipes.Prelude as Pipes

import Data.List.Index (imapM)

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
import qualified Data.IntSet as IntSet
import Data.Persistent.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.Persistent.UnionFind as UnionFind
import Data.Text.Extended.Pretty

-------------------------------------------------------------------------------

---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

data TermFragment
    = TermFragmentNode !Symbol ![TermFragment]
    | TermFragmentUVar UVar
    deriving (Eq, Ord, Show)

termFragToTruncatedTerm :: TermFragment -> Term
termFragToTruncatedTerm (TermFragmentNode s ts) = Term s (map termFragToTruncatedTerm ts)
termFragToTruncatedTerm (TermFragmentUVar uv) = Term (Symbol $ "v" <> pretty (uvarToInt uv)) []

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

-----------------------
------- Suspended constraints
-----------------------

data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
    deriving (Eq, Ord, Show)

scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

descendScs :: Int -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs =
    Sequence.filter (not . isEmptyPathTrie . scGetPathTrie) $
        fmap
            (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
            scs

-----------------------
------- UVarValue
-----------------------

data UVarValue
    = UVarUnenumerated
        { contents :: !(Maybe Node)
        , constraints :: !(Seq SuspendedConstraint)
        }
    | UVarEnumerated {termFragment :: !TermFragment}
    | UVarEliminated
    deriving (Eq, Ord, Show)

intersectUVarValue :: UVarValue -> UVarValue -> UVarValue
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
    let newContents = case (mn1, mn2) of
            (Nothing, x) -> x
            (x, Nothing) -> x
            (Just n1, Just n2) -> Just (intersect n1 n2)
        newConstraints = scs1 <> scs2
     in UVarUnenumerated newContents newConstraints
intersectUVarValue UVarEliminated _ = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ UVarEliminated = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ _ = error "intersectUVarValue: Intersecting with enumerated value not implemented"

-----------------------
------- Top-level state
-----------------------

data EnumerationState = EnumerationState
    { _uvarCounter :: UVarGen
    , _uvarRepresentative :: UnionFind
    , _uvarValues :: Seq UVarValue
    , _pruneDeps :: !(IntMap.IntMap [Term])
    {- ^ Pending prune checks keyed by suspended UVar id.

    A pruning oracle can use this to remember rewrite/template terms that
    could not be checked until a particular UVar is expanded. The pruned
    enumerator prioritizes expandable UVars that have entries here and
    rechecks the stored terms when that UVar is enumerated.
    -}
    }
    deriving (Eq, Ord, Show)

makeLensesFor
    [ ("_uvarCounter", "uvarCounter")
    , ("_uvarRepresentative", "uvarRepresentative")
    , ("_uvarValues", "uvarValues")
    ]
    ''EnumerationState

{- | Lens for the oracle's pending prune checks.

Pruning code uses this through helpers like 'getPruneDeps', 'addPruneDep', and
'deletePruneDep'. It is exported for lower-level oracles that need direct
access to the dependency map while composing their own enumeration actions.
-}
pruneDeps :: Lens' EnumerationState (IntMap.IntMap [Term])
pruneDeps = lens _pruneDeps (\s pds -> s{_pruneDeps = pds})

initEnumerationState :: Node -> EnumerationState
initEnumerationState n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
            IntMap.empty

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

type EnumerateM = StateT EnumerationState []

runEnumerateM :: EnumerateM a -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM = runStateT

-- Prune deps --

{- | Return all pending prune checks.

This is mainly useful inside a pruning oracle. A caller can inspect the map
to decide whether it is currently resuming a suspended check or starting a
fresh one from the root fragment.
-}
getPruneDeps :: EnumerateM (IntMap.IntMap [Term])
getPruneDeps = use pruneDeps

{- | Return pending prune checks for a particular UVar id.

The ids are the integer form of 'UVar's, via 'uvarToInt'. The enumerator uses
this after expanding a UVar to decide whether any previously suspended terms
should be checked against the new fragment.
-}
getPruneDepsOf :: Int -> EnumerateM (Maybe [Term])
getPruneDepsOf uv = do
    pd <- use pruneDeps
    return (pd IntMap.!? uv)

{- | Remember one term to check when the given UVar is expanded.

Oracles use this when a prune test reaches an unexpanded 'TermFragmentUVar':
store the term that needs checking, return "not pruned" for now, and let the
pruned enumerator revisit the check after that UVar becomes concrete.
-}
addPruneDep :: Int -> Term -> EnumerateM ()
addPruneDep uv rw = addPruneDeps uv [rw]

addPruneDeps :: Int -> [Term] -> EnumerateM ()
addPruneDeps uv rws = pruneDeps %= IntMap.insertWith (++) uv rws

{- | Clear pending prune checks for a UVar.

The enumerator calls this when it resumes checks for an expanded UVar. Oracles
that consume entries from 'getPruneDeps' should delete them for the same
reason: each dependency is a one-shot request to recheck after expansion.
-}
deletePruneDep :: Int -> EnumerateM ()
deletePruneDep uv = pruneDeps %= (IntMap.delete uv)

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM UVar
nextUVar = do
    c <- use uvarCounter
    let (c', uv) = UnionFind.nextUVar c
    uvarCounter .= c'
    return uv

addUVarValue :: Maybe Node -> EnumerateM UVar
addUVarValue x = do
    uv <- nextUVar
    uvarValues %= (:|> (UVarUnenumerated x Sequence.Empty))
    return uv

getUVarValue :: UVar -> EnumerateM UVarValue
getUVarValue uv = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- use uvarValues
    return $ Sequence.index values idx

getTermFragForUVar :: UVar -> EnumerateM TermFragment
getTermFragForUVar uv = termFragment <$> getUVarValue uv

getUVarRepresentative :: UVar -> EnumerateM UVar
getUVarRepresentative uv = do
    uf <- use uvarRepresentative
    let (uv', uf') = UnionFind.find uv uf
    uvarRepresentative .= uf'
    return uv'

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

---------------------
-------- Merging UVar's / nodes
---------------------

assimilateUvarVal :: UVar -> UVar -> EnumerateM ()
assimilateUvarVal uvTarg uvSrc
    | uvTarg == uvSrc = return ()
    | otherwise = do
        values <- use uvarValues
        let srcVal = Sequence.index values (uvarToInt uvSrc)
        let targVal = Sequence.index values (uvarToInt uvTarg)
        case srcVal of
            UVarEliminated -> return () -- Happens from duplicate constraints
            _ -> do
                let v = intersectUVarValue srcVal targVal
                guard (contents v /= Just EmptyNode)
                uvarValues . (ix $ uvarToInt uvTarg) .= v
                uvarValues . (ix $ uvarToInt uvSrc) .= UVarEliminated

mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    uvarValues . (ix idx) %= intersectUVarValue (UVarUnenumerated (Just n) scs)
    newValues <- use uvarValues
    guard (contents (Sequence.index newValues idx) /= Just EmptyNode)

---------------------
-------- Variant maintainer
---------------------

-- This thing here might be a performance issue. UPDATE: Yes it is; clocked at 1/3 the time and 1/2 the
-- allocations of enumerateFully
--
-- It exists because it was easier to code / might actually be faster
-- to update referenced uvars here than inline in firstExpandableUVar.
-- There is no Sequence.foldMapWithIndexM.
refreshReferencedUVars :: EnumerateM ()
refreshReferencedUVars = do
    values <- use uvarValues

    updated <-
        traverse
            ( \case
                UVarUnenumerated n scs ->
                    UVarUnenumerated n
                        <$> mapM
                            ( \sc ->
                                SuspendedConstraint (scGetPathTrie sc)
                                    <$> getUVarRepresentative (scGetUVar sc)
                            )
                            scs
                x -> return x
            )
            values

    uvarValues .= updated

---------------------
-------- Core enumeration algorithm
---------------------
--

enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node es -> enumerateEdge scs =<< lift es
                _ -> error $ "enumerateNode: unexpected node " <> show n
            (x :<| xs) -> do
                reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
                forM_ xs $ \sc -> uvarRepresentative %= UnionFind.union (scGetUVar x) (scGetUVar sc)
                uv <- getUVarRepresentative (scGetUVar x)
                mapM_ (assimilateUvarVal uv) reps

                mergeNodeIntoUVarVal uv n descendantConstraints
                return $ TermFragmentUVar uv

enumerateEdge :: Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge scs e = do
    let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
    guard $ highestConstraintIndex < length (edgeChildren e)

    newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ edgeEcs e)
    let scs' = scs <> newScs
    TermFragmentNode (edgeSymbol e) <$> imapM (\i n -> enumerateNode (descendScs i scs') n) (edgeChildren e)

---------------------
-------- Enumeration-loop control
---------------------

data ExpandableUVarResult = ExpansionStuck | ExpansionDone | ExpansionNext !UVar deriving (Show)

-- Can speed this up with bitvectors

findExpandableUVars :: EnumerateM (Maybe (IntMap.IntMap Any))
findExpandableUVars = do
    values <- use uvarValues
    -- check representative uvars because only representatives are updated
    candidateMaps <-
        mapM
            ( \i -> do
                rep <- getUVarRepresentative (intToUVar i)
                v <- getUVarValue rep
                case v of
                    (UVarUnenumerated (Just (Mu _)) Sequence.Empty) -> return IntMap.empty
                    (UVarUnenumerated (Just (Mu _)) _) -> return $ IntMap.singleton (uvarToInt rep) (Any False)
                    (UVarUnenumerated (Just _) _) -> return $ IntMap.singleton (uvarToInt rep) (Any False)
                    _ -> return IntMap.empty
            )
            [0 .. (Sequence.length values - 1)]
    let candidates = IntMap.unions candidateMaps

    if IntMap.null candidates
        then
            return Nothing
        else do
            let ruledOut =
                    foldMap
                        ( \case
                            (UVarUnenumerated _ scs) ->
                                foldMap
                                    (\sc -> IntMap.singleton (uvarToInt $ scGetUVar sc) (Any True))
                                    scs
                            _ -> IntMap.empty
                        )
                        values

            let unconstrainedCandidateMap = IntMap.filter (not . getAny) (ruledOut <> candidates)
            return (Just unconstrainedCandidateMap)

firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = do
    mb_unconstrainedCandidateMap <- findExpandableUVars
    case mb_unconstrainedCandidateMap of
        Nothing -> return ExpansionDone
        Just unconstrainedCandidateMap ->
            case IntMap.lookupMin unconstrainedCandidateMap of
                Nothing -> return ExpansionStuck
                Just (i, _) -> return $ ExpansionNext $ intToUVar i

ruleMatches :: Bool -> TermFragment -> Term -> EnumerateM Bool
-- TODO: this should match types
ruleMatches _ _ (Term (Symbol "<v>") _) = return True
ruleMatches
    pruneSuspended
    (TermFragmentNode "app" [_, _, tf_f, tf_v])
    (Term "app" [_, _, rw_f, rw_v]) = do
        rw_f_m <- ruleMatches pruneSuspended tf_f rw_f
        if not rw_f_m
            then return False
            else ruleMatches pruneSuspended tf_v rw_v
ruleMatches
    _
    (TermFragmentNode ts [_])
    (Term rws [_]) = return (ts == rws)
ruleMatches pruneSuspended (TermFragmentUVar uv) rw =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> ruleMatches pruneSuspended t rw
            _ -> return False
ruleMatches _ _ _ = return False

{- | Test whether a partially enumerated fragment represents any given term.

This is the helper a pruning oracle uses after receiving a @Left
TermFragment@ callback from 'getAllTermsPrune'. It understands the
Spectacular template shape used by the pruning code: @filter@ unwraps to its
body, @app@ compares the function and value positions, unary symbols compare
by symbol, and the term symbol @"<v>"@ is treated as a wildcard.

The Boolean argument marks checks that are allowed to suspend on unexpanded
UVars. The current matcher only follows already-enumerated UVars; callers that
need explicit suspension can pair this with 'addPruneDep'.
-}
fragRepresents :: Bool -> TermFragment -> [Term] -> EnumerateM Bool
fragRepresents pruneSuspended (TermFragmentNode "filter" [_, t]) rwrs = fragRepresents pruneSuspended t rwrs
fragRepresents pruneSuspended tf@(TermFragmentNode "app" [_, _, f, v]) rwrs = do
    tfMatches <- filterM (ruleMatches pruneSuspended tf) rwrs
    if not (null tfMatches)
        then return True
        else do
            r <- or <$> mapM (flip (fragRepresents False) rwrs) [f, v]
            return r
fragRepresents pruneSuspended tf@(TermFragmentNode _ [_]) rwrs =
    not . null <$> filterM (ruleMatches pruneSuspended tf) rwrs
fragRepresents pruneSuspended tf@(TermFragmentUVar uv) rwrs =
    do
        uvMatches <- filterM (ruleMatches pruneSuspended tf) rwrs
        if not (null uvMatches)
            then return True
            else do
                val <- getUVarValue uv
                case val of
                    UVarEnumerated t -> fragRepresents pruneSuspended t rwrs
                    _ -> return False
fragRepresents _ tf _ = error $ "unrecognized frag! " ++ show tf

enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            _ -> enumerateNode scs n

        uvarValues . (ix $ uvarToInt uv') .= UVarEnumerated t
        pd <- getPruneDepsOf (uvarToInt uv)
        case pd of
            Just rws -> do
                deletePruneDep (uvarToInt uv)
                res <- fragRepresents True t rws
                if res
                    then mzero
                    else return t
            _ -> refreshReferencedUVars >> return t

enumerateOutFirstExpandableUVar :: EnumerateM ()
enumerateOutFirstExpandableUVar = do
    muv <- firstExpandableUVar
    case muv of
        ExpansionNext uv -> void $ enumerateOutUVar uv
        ExpansionDone -> mzero
        ExpansionStuck -> mzero

enumerateFully :: EnumerateM ()
enumerateFully = const () <$> enumerateFully' () False (\x _ _ -> return (False, x))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each expandable UVar:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the current ECTA already represents a forbidden
  template.
* @Left fragment@ is passed after expansion, so callers can reject the
  concrete fragment or update their oracle state before enumeration
  continues.

The threaded state parameter belongs to the caller. Returning @True@ prunes
the current nondeterministic branch; returning @False@ keeps it. When
@usePruneHints@ is enabled, UVar ids in 'pruneDeps' are expanded first so
suspended checks resume promptly.
-}
enumerateFully' ::
    forall a.
    a ->
    Bool ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    EnumerateM Bool
enumerateFully' ost usePruneHints oracle = do
    muv <-
        if usePruneHints
            then do
                hints <- IntMap.keysSet <$> getPruneDeps
                if IntSet.null hints
                    -- if we aren't targeting any terms, just expand the first one
                    then {-# SCC "no-hints" #-} firstExpandableUVar
                    else do
                        expandable <- findExpandableUVars
                        case expandable of
                            Nothing -> return ExpansionDone
                            Just ucm | IntMap.null ucm -> return ExpansionStuck
                            Just ucm ->
                                let expSet = IntMap.keysSet ucm
                                    inters = IntSet.intersection expSet hints
                                 in if not (IntSet.null inters)
                                        then
                                            return $
                                                ExpansionNext $
                                                    intToUVar (IntSet.findMax inters)
                                        else firstExpandableUVar
            else firstExpandableUVar
    case muv of
        ExpansionStuck -> mzero
        ExpansionDone -> return True
        ExpansionNext uv ->
            let continue ost' = do
                    tf <- enumerateOutUVar uv
                    (should_prune, ost'') <- oracle ost' uv (Left tf)
                    if should_prune
                        then mzero
                        else enumerateFully' ost'' usePruneHints oracle
             in do
                    UVarUnenumerated (Just n) scs <- getUVarValue uv
                    case n of
                        Mu _ | scs == Sequence.empty -> return True
                        _ -> do
                            (should_prune, ost') <- oracle ost uv (Right n)
                            if should_prune then mzero else continue ost'

---------------------
-------- Expanding an enumerated term fragment into a term
---------------------

{- | Expand a fragment even if it still contains unenumerated UVars.

Unlike 'expandTermFrag', this is safe for diagnostics and oracle logging while
enumeration is still in progress. Unexpanded non-recursive UVars become
placeholders named @<vN>@, where @N@ is the UVar id; recursive holes become
@Mu@.
-}
expandPartialTermFrag :: TermFragment -> EnumerateM Term
expandPartialTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandPartialTermFrag ts
expandPartialTermFrag (TermFragmentUVar uv) =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> expandPartialTermFrag t
            UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
            _ -> return $ Term (Symbol $ "<v" <> pretty (uvarToInt uv) <> ">") []

expandTermFrag :: TermFragment -> EnumerateM Term
expandTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandTermFrag ts
expandTermFrag (TermFragmentUVar uv) =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> expandTermFrag t
            UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
            _ ->
                error "expandTermFrag: Non-recursive, unenumerated node encountered"

expandUVar :: UVar -> EnumerateM Term
expandUVar uv = do
    UVarEnumerated t <- getUVarValue uv
    expandTermFrag t

---------------------
-------- Full enumeration
---------------------

getAllTruncatedTerms :: Node -> [Term]
getAllTruncatedTerms n = map (termFragToTruncatedTerm . fst) $
    flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        getTermFragForUVar (intToUVar 0)

{- | Enumerate terms while letting an oracle prune branches.

This is the public entry point for pruning-aware enumeration. The oracle has
type:

@
state -> UVar -> Either TermFragment Node -> EnumerateM (Bool, state)
@

It receives the caller state, the UVar being considered, and either the node
about to be expanded (@Right@) or the fragment just produced (@Left@). Return
@True@ to discard that branch, or @False@ with updated state to keep
enumerating. A typical Spectacular-style oracle uses @Right node@ with
'nodeRepresentsTemplate' to reject whole ECTA branches, and @Left fragment@
with 'fragRepresents' to reject terms that match known rewrites/templates.
-}
getAllTermsPrune ::
    forall a.
    a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    Node ->
    [Term]
getAllTermsPrune ost oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ enumPrune ost oracle

{- | Monadic form of 'getAllTermsPrune'.

Use this when the caller is already composing lower-level enumeration actions
in 'EnumerateM'. Most callers should prefer 'getAllTermsPrune'.
-}
enumPrune :: forall a. a -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) -> EnumerateM Term
enumPrune a oracle = do
    finished <- enumerateFully' a True oracle
    if finished then expandUVar (intToUVar 0) else mzero

getAllTerms :: Node -> [Term]
getAllTerms = getAllTermsPrune () (\_ _ _ -> return (False, ()))

{- | Inefficient enumeration

For ECTAs with 'Mu' nodes may produce an infinite list or may loop indefinitely, depending on the ECTAs. For example, for

> createMu $ \r -> Node [Edge "f" [r], Edge "a" []]

it will produce

> [ Term "a" []
> , Term "f" [Term "a" []]
> , Term "f" [Term "f" [Term "a" []]]
> , ...
> ]

This happens to work currently because non-recursive edges are interned before recursive edges.

TODO: It would be much nicer if this did fair enumeration. It would avoid the beforementioned dependency on interning
order, and it would give better enumeration for examples such as

> Node [Edge "h" [
>     createMu $ \r -> Node [Edge "f" [r], Edge "a" []]
>   , createMu $ \r -> Node [Edge "g" [r], Edge "b" []]
>   ]]

This will currently produce

> [ Term "h" [Term "a" [], Term "b" []]
> , Term "h" [Term "a" [], Term "g" [Term "b" []]]
> , Term "h" [Term "a" [], Term "g" [Term "g" [Term "b" []]]]
> , ..
> ]

where it always unfolds the /second/ argument to @h@, never the first.
-}
naiveDenotation :: Node -> [Term]
naiveDenotation = naiveDenotationBounded Nothing

{- | Naive denotation with an optional bound on recursive unfolding.

If the bound is @Just n@, at most @n@ levels of 'Mu' unfolding are explored. If
the bound is @Nothing@, recursive nodes are unfolded without a bound, matching
'naiveDenotation'. This is useful for tests and sanity checks where fully naive
enumeration would otherwise produce an infinite list.
-}
naiveDenotationBounded :: Maybe Int -> Node -> [Term]
naiveDenotationBounded maxDepth node = Pipes.toList $ every (go maxDepth node)
  where
    -- \| Note that this code uses the decision that f(a,a) does not satisfy the constraint 0.0=1.0 because those paths are empty.
    --   It would be equally valid to say that it does.
    ecsSatisfied :: Term -> EqConstraints -> Bool
    ecsSatisfied t ecs =
        all
            (eclassSatisfied t)
            (map unPathEClass $ unsafeGetEclasses ecs)

    eclassSatisfied :: Term -> [Path] -> Bool
    eclassSatisfied _ [] = True
    eclassSatisfied t (p : ps) = isJust pathValue && all (\p' -> pathValue == getPath p' t) ps
      where
        pathValue = getPath p t

    go :: Maybe Int -> Node -> ListT Identity Term
    go _ EmptyNode = mzero
    go mbDepth n@(Mu _) = case mbDepth of
        Nothing -> go Nothing (unfoldOuterRec n)
        Just d
            | d <= 0 -> mzero
            | otherwise -> go (Just $ d - 1) (unfoldOuterRec n)
    go _ (Rec _) = error "naiveDenotation: unexpected Rec"
    go mbDepth (Node es) = do
        e <- Select $ each es

        children <- mapM (go mbDepth) (edgeChildren e)

        let res = Term (edgeSymbol e) children
        guard $ ecsSatisfied res (edgeEcs e)
        return res
