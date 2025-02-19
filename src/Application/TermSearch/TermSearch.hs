{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Application.TermSearch.TermSearch where

import           Data.List                      ( (\\)
                                                , permutations
                                                )
import           Data.List.Extra                ( nubOrd )
import qualified Data.Map                      as Map
import           Data.Maybe                     ( fromMaybe )
import           Data.Text                      ( Text )
import           Data.Tuple                     ( swap )
import           System.IO                      ( hFlush
                                                , stdout
                                                )

import           Data.ECTA
import           Data.ECTA.Paths
import           Data.ECTA.Term
import           Data.Text.Extended.Pretty
import           Utility.Fixpoint

import           Application.TermSearch.Dataset
import           Application.TermSearch.Type
import           Application.TermSearch.Utils

------------------------------------------------------------------------------

tau :: Node
tau = createMu
  (\n -> union
    (  [arrowType n n, var1, var2, var3, var4]
    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
    )
  )
 where
  constructorToEdge :: Node -> (Text, Int) -> Edge
  constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

  usedConstructors = allConstructors

allConstructors :: [(Text, Int)]
allConstructors =
  nubOrd (concatMap getConstructors (Map.keys hoogleComponents))
    \\ [("Fun", 2)]
 where
  getConstructors :: TypeSkeleton -> [(Text, Int)]
  getConstructors (TVar _    ) = []
  getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
  getConstructors (TCons nm ts) =
    (nm, length ts) : concatMap getConstructors ts

generalize :: Node -> Node
generalize n@(Node [_]) = Node
  [mkEdge s ns' (mkEqConstraints $ map pathsForVar vars)]
 where
  vars                = [var1, var2, var3, var4, varAcc]
  nWithVarsRemoved    = mapNodes (\x -> if x `elem` vars then tau else x) n
  (Node [Edge s ns']) = nWithVarsRemoved

  pathsForVar :: Node -> [Path]
  pathsForVar v = pathsMatching (== v) n
generalize n = error $ "cannot generalize: " ++ show n

-- Use of `getPath (path [0, 2]) n1` instead of `tau` effectively pre-computes some reduction.
-- Sometimes this can be desirable, but for enumeration,
app :: Node -> Node -> Node
app n1 n2 = Node
  [ mkEdge
      "app"
      [tau, theArrowNode, n1, n2]
      (mkEqConstraints
        [ [path [1], path [2, 0, 0]]
        , [path [3, 0], path [2, 0, 1]]
        , [path [0], path [2, 0, 2]]
        ]
      )
  ]

--------------------------------------------------------------------------------
------------------------------- Relevancy Encoding -----------------------------
--------------------------------------------------------------------------------

applyOperator :: Node
applyOperator = Node
  [ constFunc
    "$"
    (generalize $ arrowType (arrowType var1 var2) (arrowType var1 var2))
  , constFunc "id" (generalize $ arrowType var1 var1)
  ]

hoogleComps :: [Edge]
hoogleComps =
  filter
      (\e ->
        edgeSymbol e
          `notElem` map (Symbol . toMappedName) speciallyTreatedFunctions
      )
    $ map (uncurry parseHoogleComponent . swap)
    $ Map.toList hoogleComponents

anyFunc :: Node
anyFunc = Node hoogleComps

filterType :: Node -> Node -> Node
filterType n t =
  Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

termsK :: Node -> Bool -> Int -> [Node]
termsK _      _     0 = []
termsK anyArg False 1 = [anyArg, anyFunc]
termsK anyArg True  1 = [anyArg, anyFunc, applyOperator]
termsK anyArg _ 2 =
  [ app anyListFunc (union [anyNonNilFunc, anyArg, applyOperator])
  , app fromJustFunc (union [anyNonNothingFunc, anyArg, applyOperator])
  , app (union [anyNonListFunc, anyArg]) (union (termsK anyArg True 1))
  ]
termsK anyArg _ k = map constructApp [1 .. (k - 1)]
 where
  constructApp :: Int -> Node
  constructApp i =
    app (union (termsK anyArg False i)) (union (termsK anyArg True (k - i)))

relevantTermK :: Node -> Bool -> Int -> [Argument] -> [Node]
relevantTermK anyArg includeApplyOp k []       = termsK anyArg includeApplyOp k
relevantTermK _      _              1 [(x, t)] = [Node [constArg x t]]
relevantTermK anyArg _ k argNames
  | k < length argNames = []
  | otherwise = concatMap (\i -> map (constructApp i) allSplits) [1 .. (k - 1)]
 where
  allSplits = map (`splitAt` argNames) [0 .. (length argNames)]

  constructApp :: Int -> ([Argument], [Argument]) -> Node
  constructApp i (xs, ys) =
    let f = union (relevantTermK anyArg False i xs)
        x = union (relevantTermK anyArg True (k - i) ys)
    in  app f x

relevantTermsOfSize :: Node -> [Argument] -> Int -> Node
relevantTermsOfSize anyArg args k = union $ concatMap (relevantTermK anyArg True k) (permutations args)

relevantTermsUptoK :: Node -> [Argument] -> Int -> Node
relevantTermsUptoK anyArg args k = union (map (relevantTermsOfSize anyArg args) [1 .. k])

prettyTerm :: Term -> Term
prettyTerm (Term "app" ns) = Term
  "app"
  [prettyTerm (ns !! (length ns - 2)), prettyTerm (ns !! (length ns - 1))]
prettyTerm (Term "filter" ns) = prettyTerm (last ns)
prettyTerm (Term s        _ ) = Term s []

dropTypes :: Node -> Node
dropTypes (Node es) = Node (map dropEdgeTypes es)
 where
  dropEdgeTypes (Edge "app" [_, _, a, b]) =
    Edge "app" [dropTypes a, dropTypes b]
  dropEdgeTypes (Edge "filter" [_, a]) = Edge "filter" [dropTypes a]
  dropEdgeTypes (Edge s        [_]   ) = Edge s []
  dropEdgeTypes e                      = e
dropTypes n = n

getText :: Symbol -> Text
getText (Symbol s) = s

--------------------------
-------- Remove uninteresting terms
--------------------------

fromJustFunc :: Node
fromJustFunc =
  Node $ filter (\e -> edgeSymbol e `elem` maybeFunctions) hoogleComps

maybeFunctions :: [Symbol]
maybeFunctions =
  [ "Data.Maybe.fromJust"
  , "Data.Maybe.maybeToList"
  , "Data.Maybe.isJust"
  , "Data.Maybe.isNothing"
  ]

listReps :: [Text]
listReps = map
  toMappedName
  [ "Data.Maybe.listToMaybe"
  , "Data.Either.lefts"
  , "Data.Either.rights"
  , "Data.Either.partitionEithers"
  , "Data.Maybe.catMaybes"
  , "GHC.List.head"
  , "GHC.List.last"
  , "GHC.List.tail"
  , "GHC.List.init"
  , "GHC.List.null"
  , "GHC.List.length"
  , "GHC.List.reverse"
  , "GHC.List.concat"
  , "GHC.List.concatMap"
  , "GHC.List.sum"
  , "GHC.List.product"
  , "GHC.List.maximum"
  , "GHC.List.minimum"
  , "(GHC.List.!!)"
  , "(GHC.List.++)"
  ]

isListFunction :: Symbol -> Bool
isListFunction (Symbol sym) = sym `elem` listReps

maybeReps :: [Text]
maybeReps = map
  toMappedName
  [ "Data.Maybe.maybeToList"
  , "Data.Maybe.isJust"
  , "Data.Maybe.isNothing"
  , "Data.Maybe.fromJust"
  ]

isMaybeFunction :: Symbol -> Bool
isMaybeFunction (Symbol sym) = sym `elem` maybeReps

anyListFunc :: Node
anyListFunc = Node $ filter (isListFunction . edgeSymbol) hoogleComps

anyNonListFunc :: Node
anyNonListFunc = Node $ filter
  (\e -> not (isListFunction (edgeSymbol e))
    && not (isMaybeFunction (edgeSymbol e))
  )
  hoogleComps

anyNonNilFunc :: Node
anyNonNilFunc =
  Node $ filter (\e -> edgeSymbol e /= Symbol (toMappedName "Nil")) hoogleComps

anyNonNothingFunc :: Node
anyNonNothingFunc = Node $ filter
  (\e -> edgeSymbol e /= Symbol (toMappedName "Data.Maybe.Nothing"))
  hoogleComps

--------------------------------------------------------------------------------

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
-- reduceFully = fixUnbounded (reducePartially)

checkSolution :: Term -> [Term] -> IO ()
checkSolution _ [] = return ()
checkSolution target (s : solutions)
  | prettyTerm s == target = print $ pretty (prettyTerm s)
  | otherwise = do
    -- print $ pretty (prettyTerm s)
    -- print (s)
    checkSolution target solutions

reduceFullyAndLog :: Node -> IO Node
reduceFullyAndLog = go 0
 where
  go :: Int -> Node -> IO Node
  go i n = do
    putStrLn
      $  "Round "
      ++ show i
      ++ ": "
      ++ show (nodeCount n)
      ++ " nodes, "
      ++ show (edgeCount n)
      ++ " edges"
    hFlush stdout
    -- putStrLn $ renderDot $ toDot n
    -- print n
    let n' = withoutRedundantEdges (reducePartially n)
    if n == n' || i >= 30 then return n else go (i + 1) n'

--------------------------------------------------------------------------------
--------------------------------- Test Functions -------------------------------
--------------------------------------------------------------------------------

f1 :: Edge
f1 = constFunc "Nothing" (maybeType tau)

f2 :: Edge
f2 = constFunc "Just" (generalize $ arrowType var1 (maybeType var1))

f3 :: Edge
f3 = constFunc
  "fromMaybe"
  (generalize $ arrowType var1 (arrowType (maybeType var1) var1))

f4 :: Edge
f4 = constFunc "listToMaybe"
               (generalize $ arrowType (listType var1) (maybeType var1))

f5 :: Edge
f5 = constFunc "maybeToList"
               (generalize $ arrowType (maybeType var1) (listType var1))

f6 :: Edge
f6 = constFunc
  "catMaybes"
  (generalize $ arrowType (listType (maybeType var1)) (listType var1))

f7 :: Edge
f7 = constFunc
  "mapMaybe"
  (generalize $ arrowType (arrowType var1 (maybeType var2))
                          (arrowType (listType var1) (listType var2))
  )

f8 :: Edge
f8 = constFunc "id" (generalize $ arrowType var1 var1)

f9 :: Edge
f9 = constFunc
  "replicate"
  (generalize $ arrowType (constrType0 "Int") (arrowType var1 (listType var1)))

f10 :: Edge
f10 = constFunc
  "foldr"
  (generalize $ arrowType (arrowType var1 (arrowType var2 var2))
                          (arrowType var2 (arrowType (listType var1) var2))
  )

f11 :: Edge
f11 = constFunc
  "iterate"
  (generalize $ arrowType (arrowType var1 var1) (arrowType var1 (listType var1))
  )

f12 :: Edge
f12 = constFunc
  "(!!)"
  (generalize $ arrowType (listType var1) (arrowType (constrType0 "Int") var1))

f13 :: Edge
f13 = constFunc
  "either"
  (generalize $ arrowType
    (arrowType var1 var3)
    (arrowType (arrowType var2 var3)
               (arrowType (constrType2 "Either" var1 var2) var3)
    )
  )

f14 :: Edge
f14 = constFunc
  "Left"
  (generalize $ arrowType var1 (constrType2 "Either" var1 var2))

f15 :: Edge
f15 = constFunc "id" (generalize $ arrowType var1 var1)

f16 :: Edge
f16 = constFunc
  "(,)"
  (generalize $ arrowType var1 (arrowType var2 (constrType2 "Pair" var1 var2)))

f17 :: Edge
f17 =
  constFunc "fst" (generalize $ arrowType (constrType2 "Pair" var1 var2) var1)

f18 :: Edge
f18 =
  constFunc "snd" (generalize $ arrowType (constrType2 "Pair" var1 var2) var2)

f19 :: Edge
f19 = constFunc
  "foldl"
  (generalize $ arrowType (arrowType var2 (arrowType var1 var2))
                          (arrowType var2 (arrowType (listType var1) var2))
  )

f20 :: Edge
f20 = constFunc
  "swap"
  ( generalize
  $ arrowType (constrType2 "Pair" var1 var2) (constrType2 "Pair" var2 var1)
  )

f21 :: Edge
f21 = constFunc
  "curry"
  (generalize $ arrowType (arrowType (constrType2 "Pair" var1 var2) var3)
                          (arrowType var1 (arrowType var2 var3))
  )

f22 :: Edge
f22 = constFunc
  "uncurry"
  (generalize $ arrowType (arrowType var1 (arrowType var2 var3))
                          (arrowType (constrType2 "Pair" var1 var2) var3)
  )

f23 :: Edge
f23 = constFunc "head" (generalize $ arrowType (listType var1) var1)

f24 :: Edge
f24 = constFunc "last" (generalize $ arrowType (listType var1) var1)

f25 :: Edge
f25 = constFunc
  "Data.ByteString.foldr"
  (generalize $ arrowType
    (arrowType (constrType0 "Word8") (arrowType var2 var2))
    (arrowType var2 (arrowType (constrType0 "ByteString") var2))
  )

f26 :: Edge
f26 = constFunc
  "unfoldr"
  (generalize $ arrowType
    (arrowType var1 (maybeType (constrType2 "Pair" (constrType0 "Word8") var1)))
    (arrowType var1 (constrType0 "ByteString"))
  )

f27 :: Edge
f27 = constFunc
  "Data.ByteString.foldrChunks"
  (generalize $ arrowType
    (arrowType (constrType0 "ByteString") (arrowType var2 var2))
    (arrowType var2 (arrowType (constrType0 "ByteString") var2))
  )

f28 :: Edge
f28 = constFunc
  "bool"
  ( generalize
  $ arrowType var1 (arrowType var1 (arrowType (constrType0 "Bool") var1))
  )

f29 :: Edge
f29 = constFunc
  "lookup"
  (generalize $ arrowType
    (constrType1 "@@hplusTC@@Eq" var1)
    (arrowType var1 (arrowType (constrType2 "Pair" var1 var2) (maybeType var2)))
  )

f30 :: Edge
f30 = constFunc "nil" (generalize $ listType var1)

--------------------------
------ Util functions
--------------------------

toMappedName :: Text -> Text
toMappedName x = fromMaybe x (Map.lookup x groupMapping)

prettyPrintAllTerms :: AblationType -> Term -> Node -> IO ()
prettyPrintAllTerms ablation sol n = do
  putStrLn $ "Expected: " ++ show (pretty sol)
  let ts = case ablation of
             NoEnumeration -> naiveDenotation n
             NoOptimize    -> naiveDenotation n
             _             -> getAllTerms n
  checkSolution sol ts

substTerm :: Term -> Term
substTerm (Term (Symbol sym) ts) =
  Term (Symbol $ fromMaybe sym (Map.lookup sym groupMapping)) (map substTerm ts)

parseHoogleComponent :: Text -> TypeSkeleton -> Edge
parseHoogleComponent name t =
  constFunc (Symbol name) (generalize $ typeToFta t)
