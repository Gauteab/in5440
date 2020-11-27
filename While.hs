{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoImplicitPrelude #-}

import Control.Lens
import Data.Data (Data)
import Data.Data.Lens (biplate)
import qualified Data.IntMap.Strict as Map
import qualified Data.Set as Set

-- import Data.Text (Text)
import Relude

-- import Text.Pretty.Simple (pPrint)
import qualified Text.Show

--- AST ---

type Program = S

data S
  = Assignment Assignment
  | S ::: S -- Sequence Statements
  | Skip
  | If BExp S S
  | While BExp S
  deriving (Show)

infixr 5 :::

newtype Identifier
  = Identifier String
  deriving (Eq, Data, Ord)
  deriving (Show) via String

instance IsString Identifier where
  fromString = Identifier

data Assignment
  = Identifier := AExp
  deriving (Show, Data)

data AExp
  = Variable Identifier
  | Number Int
  | BinaryArithmetic ArithmeticOperator AExp AExp
  deriving (Ord, Eq, Data)

deriving instance Plated AExp

instance Show AExp where
  show (Variable (Identifier i)) = i
  show (Number i) = show i
  show (BinaryArithmetic op a1 a2) = show a1 ++ " " ++ op ++ " " ++ show a2

data BExp
  = True'
  | False'
  | Not BExp
  | BinaryBoolean BooleanOperator BExp BExp
  | BinaryRelational RelationalOperator AExp AExp
  deriving (Show, Data)

deriving instance Plated BExp

type ArithmeticOperator = String
type RelationalOperator = String
type BooleanOperator = String

makePrisms ''AExp

--- Analysis ---

type LabelMap a = IntMap (Set a)

data CFG = CFG
  { _blocks :: IntMap Block
  , _edges :: IntMap [Label]
  }
  deriving (Show, Data)

deriving instance Plated CFG

type Flow = [(Label, Label)]

allEdges :: CFG -> Flow
allEdges (CFG _ edg) =
  [ (from, to)
  | (from, vs) <- Map.toList edg
  , to <- vs
  ]

makeGraph :: Label -> [Block] -> [Label] -> CFG
makeGraph label blocks edges =
  CFG
    { _blocks = Map.fromList $ zip (repeat label) blocks
    , _edges = Map.singleton label edges
    }

instance Semigroup CFG where
  (CFG blocks1 edges1) <> (CFG blocks2 edges2) =
    CFG (blocks1 <> blocks2) (Map.unionWith (<>) edges1 edges2)

instance Monoid CFG where
  mempty = CFG mempty mempty

type Label = Int

data Block = AssignmentBlock Assignment | Expression AExp | Conditional BExp
  deriving (Show, Data)

deriving instance Plated Block
makePrisms ''Block

controlFlowGraph :: Program -> CFG
controlFlowGraph = flip evalState 0 . f
  where
    f :: S -> State Label CFG
    f = \case
      s1 ::: s2 -> do
        label1 <- get
        g1 <- f s1
        label2 <- get
        g2 <- f s2
        pure $ g1 <> g2 <> makeGraph label1 [] [label2]
      Assignment a -> do
        label <- freshLabel
        pure $ makeGraph label [AssignmentBlock a] []
      While condition body -> do
        label <- freshLabel
        bodyGraph <- f body
        lastBodyLabel <- gets (subtract 1)
        let blocks = Map.singleton label (Conditional condition)
            edges = Map.fromList [(lastBodyLabel, [label]), (label, [label + 1])]
        pure $ CFG blocks edges <> bodyGraph

freshLabel :: State Label Label
freshLabel = state $ id &&& (+ 1) -- relude exports (&&&)

--- Worklist Algorithm ---

allAExp :: Block -> Set AExp
allAExp = Set.fromList . toListOf (biplate . cosmos . filteredBy _BinaryArithmetic)

identifiers :: Data a => a -> Set Identifier
identifiers = toSetOf biplate

toSetOf :: Ord a => Getting (Endo [a]) s a -> s -> Set a
toSetOf l = Set.fromList . toListOf l

uses :: Block -> Set Identifier
uses (AssignmentBlock (_ := a)) = identifiers a
uses a = identifiers a

defines :: Block -> Set Identifier
defines (AssignmentBlock (x := _)) = Set.singleton x
defines _ = Set.empty

data MonotoneFramework a = MF
  { extremal :: Flow -> Set Label
  , ι :: CFG -> Set a
  , (⊥) :: CFG -> Set a
  , transfer :: CFG -> Set a -> Label -> Set a
  , (⊑) :: Set a -> Set a -> Bool
  , (⨆) :: Set a -> Set a -> Set a
  , flow :: CFG -> Flow
  }

--- Reaching definitions ---

type RDEntry = (Identifier, Maybe Label)

rdTransfer :: CFG -> Set RDEntry -> Label -> Set RDEntry
rdTransfer cfg old l = gen <> (old Set.\\ kill)
  where
    Just block = Map.lookup l $ _blocks cfg
    gen = Set.map (,Just l) $ defines block
    kill = Set.filter ((`Set.member` killSet) . fst) old
      where
        killSet = defines block

rd :: MonotoneFramework RDEntry
rd =
  MF
    { extremal = const (Set.singleton 0)
    , ι = Set.map (,Nothing) . identifiers
    , (⊥) = const Set.empty
    , (⊑) = Set.isSubsetOf
    , (⨆) = Set.union
    , transfer = rdTransfer
    , flow = allEdges
    }

--- Available expressions ---

type AEEntry = AExp

aeTransfer :: CFG -> Set AEEntry -> Label -> Set AEEntry
aeTransfer cfg old l = (old Set.\\ kill) <> gen
  where
    Just block = Map.lookup l $ _blocks cfg
    gen = allAExp block
    kill = Set.filter (not . (`Set.disjoint` killSet) . toSetOf biplate) old
      where
        killSet = defines block

-- ⊥
-- UP TACK
-- Unicode: U+22A5, UTF-8: E2 8A A5

-- ⊑
-- N-ARY SQUARE UNION OPERATOR
-- Unicode: U+2A06, UTF-8: E2 A8 86

-- SQUARE IMAGE OF OR EQUAL TO
-- Unicode: U+2291, UTF-8: E2 8A 91

-- ι
-- GREEK SMALL LETTER IOTA
-- Unicode: U+03B9, UTF-8: CE B9

ae :: MonotoneFramework AEEntry
ae =
  MF
    { extremal = const (Set.singleton 0)
    , ι = const Set.empty
    , (⊥) = foldMap allAExp . _blocks
    , (⊑) = flip Set.isSubsetOf
    , (⨆) = Set.intersection
    , transfer = aeTransfer
    , flow = allEdges
    }

-- Very busy expressions

type VBEntry = AExp

vbTransfer :: CFG -> Set VBEntry -> Label -> Set VBEntry
vbTransfer = aeTransfer

findExtremal :: Flow -> Set Label
findExtremal edges = Set.fromList . filter (noInEdges edges) . map fst $ edges
  where
    noInEdges :: Flow -> Label -> Bool
    noInEdges edges l = all ((/= l) . snd) edges

vb :: MonotoneFramework AEEntry
vb =
  MF
    { extremal = findExtremal
    , ι = const Set.empty
    , (⊥) = foldMap allAExp . _blocks
    , (⊑) = flip Set.isSubsetOf
    , (⨆) = Set.intersection
    , transfer = vbTransfer
    , flow = fmap swap . allEdges
    }

-- worklist :: Ord a => MonotoneFramework a -> CFG -> LabelMap (a, a)
worklist :: MonotoneFramework a -> CFG -> IntMap (Set a, Set a)
worklist MF{..} cfg = result $ go (flow cfg) initialMap
  where
    initialMap = Map.fromList $ zip (Set.toList . extremal $ flow cfg) (repeat . ι $ cfg)
    result = Map.mapWithKey (\l pre -> (pre, transfer cfg pre l))
    go [] !output = output
    go ((l, l') : rest) !output =
      let analysisPre = Map.lookup l output ?: (⊥) cfg
          analysisPost = Map.lookup l' output ?: (⊥) cfg
          new = transfer cfg analysisPre l
          newset = new ⨆ analysisPost
          output' = Map.insert l' newset output
          edges = filter ((== l') . fst) $ flow cfg
       in if new ⊑ analysisPost
            then go rest output
            else go (edges ++ rest) output'

present :: Show a => IntMap (Set a, Set a) -> IO ()
present = traverse_ f . Map.toList
  where
    f (l, (a, b)) = putStrLn $ show l ++ ": " ++ show (Set.toList a) ++ " " ++ show (Set.toList b)

--- Main ---

--[y:=x]0; [z:=1]1; while [y>1]2 do ([z:=z*y]3; [y:=y-1]4); [y:=0]5
factorial :: Program
factorial =
  Assignment ("y" := Variable "x")
    ::: Assignment ("z" := Number 1)
    ::: While
      (BinaryRelational ">" (Variable "y") (Number 1))
      ( Assignment ("z" := BinaryArithmetic "*" (Variable "z") (Variable "y"))
          ::: Assignment ("y" := BinaryArithmetic "-" (Variable "y") (Number 1))
      )
    ::: Assignment ("y" := Number 0)

cfg :: CFG
cfg = controlFlowGraph factorial

block :: Block
block = AssignmentBlock ("z" := BinaryArithmetic "*" (BinaryArithmetic "+" (BinaryArithmetic "-" (Number 3) (Number 1)) (Number 1)) (Variable "y"))

aexp :: AExp
aexp = BinaryArithmetic "*" (BinaryArithmetic "+" (BinaryArithmetic "-" (Number 3) (Number 1)) (Number 1)) (Variable "y")

bexp :: BExp
bexp = BinaryRelational ">" (Variable "y") (BinaryArithmetic "+" (Number 3) (Number 1))

main :: IO ()
main = do
  let cfg = controlFlowGraph factorial
  -- present $ worklist ae cfg
  -- present $ worklist rd cfg
  present $ worklist vb cfg

-- spec :: Spec
-- spec = do
--   let factorialCFG =
--         Map.fromList
--           [ (1, (AssignmentBlock , Edge 2))
--           , (2, (AssignmentBlock, Edge 3))
--           , (3, (AssignmentBlock, Branch 4 6))
--           , (4, (AssignmentBlock, Edge 5))
--           , (5, (AssignmentBlock, Edge 3))
--           ]
--   describe "control flow graph" $ do
--     it "can retrieve edges" $ do
--       edges 2 factorialCFG `shouldBe` [3, 5]
--       edges 5 factorialCFG `shouldBe` []
--     it "can be constructed from factorial program" $ do
--       controlFlowGraph factorial `shouldBe` factorialCFG
