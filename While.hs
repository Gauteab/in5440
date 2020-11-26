{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

import qualified Debug.Trace as Debug

import Control.Lens
import Data.Data (Data)
import Data.Data.Lens (biplate)
import qualified Data.IntMap.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Relude
import Text.Pretty.Simple (pPrint)
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

type Identifier = String

data Assignment
  = Identifier := AExp
  deriving (Show)

data AExp
  = Variable Identifier
  | Number Int
  | BinaryArithmetic ArithmeticOperator AExp AExp
  deriving (Ord, Eq, Data)

deriving instance Plated AExp

instance Show AExp where
  show (Variable i) = i
  show (Number i) = show i
  show (BinaryArithmetic op a1 a2) = show a1 ++ " " ++ op ++ " " ++ show a2

data BExp
  = True'
  | False'
  | Not BExp
  | BinaryBoolean BooleanOperator BExp BExp
  | BinaryRelational RelationalOperator AExp AExp
  deriving (Show, Data)

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
  deriving (Show)

allEdges :: CFG -> [(Label, Label)]
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
  deriving (Show)

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
      (Assignment a) -> do
        label <- freshLabel
        pure $ makeGraph label [AssignmentBlock a] []
      (While condition body) -> do
        label <- freshLabel
        bodyGraph <- f body
        lastBodyLabel <- gets (subtract 1)
        let blocks = Map.singleton label (Conditional condition)
        let edges = Map.fromList [(lastBodyLabel, [label]), (label, [label + 1])]
        pure $ CFG blocks edges <> bodyGraph

freshLabel :: State Label Label
freshLabel = state $ id &&& (+ 1) -- relude exports (&&&)

--- Worklist Algorithm ---

-- Find all arithmetic expressions
allAExp :: Block -> Set AExp
allAExp (AssignmentBlock (_ := a)) = allAExpA a
allAExp (Expression a) = allAExpA a
allAExp (Conditional bexp) = allAExpB bexp

allAExpA :: AExp -> Set AExp
allAExpA = Set.fromList . toListOf (cosmos . filteredBy _BinaryArithmetic)

-- allAExpA (Variable _) = Set.empty
-- allAExpA (Number _) = Set.empty
-- allAExpA e@(BinaryArithmetic _ a1 a2) =
--   allAExpA a1 <> allAExpA a2 <> Set.singleton e

allAExpB :: BExp -> Set AExp
allAExpB = Set.fromList . toListOf biplate

-- allAExpB (Not exp) = allAExpB exp
-- allAExpB (BinaryBoolean _ b1 b2) = on Set.union allAExpB b1 b2
-- allAExpB (BinaryRelational _ a1 a2) = on Set.union allAExpA a1 a2
-- allAExpB _ = Set.empty

-------------------------------

occursIn :: AExp -> Set Identifier
occursIn (Variable ident) = Set.singleton ident
occursIn (Number _) = Set.empty
occursIn (BinaryArithmetic _ a1 a2) = on Set.union occursIn a1 a2

occursInB :: BExp -> Set Identifier
occursInB (Not exp) = occursInB exp
occursInB (BinaryBoolean _ b1 b2) = on Set.union occursInB b1 b2
occursInB (BinaryRelational _ a1 a2) = on Set.union occursIn a1 a2
occursInB _ = Set.empty

identifiers :: CFG -> Set Identifier
identifiers = foldMap f . _blocks
  where
    f (AssignmentBlock (x := y)) = Set.singleton x <> fa y
    f (Expression a) = fa a
    f (Conditional bexp) = fb bexp
    fa (Variable x) = Set.singleton x
    fa (BinaryArithmetic _ x y) = fa x <> fa y
    fa _ = Set.empty
    fb (Not e) = fb e
    fb (BinaryBoolean _ x y) = fb x <> fb y
    fb (BinaryRelational _ x y) = fa x <> fa y

uses :: Block -> Set Identifier
uses (AssignmentBlock (_ := a)) = occursIn a
uses (Expression a) = occursIn a
uses (Conditional bexp) = occursInB bexp

defines :: Block -> Set Identifier
defines (AssignmentBlock (x := _)) = Set.singleton x
defines _ = Set.empty

data Analysis
  = ReachableDefinition
  | LiveVariable
  | VeryBusy
  | AvailableExpr
  deriving (Show, Eq, Ord, Bounded, Enum)

data MonotoneFramework a = MF
  { extremal :: CFG -> Set Label
  , init :: CFG -> Set a
  , bottom :: CFG -> Set a
  , transfer :: CFG -> Set a -> Label -> Set a
  , latticeLess :: Set a -> Set a -> Bool
  , latticeJoin :: Set a -> Set a -> Set a
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
    , init = Set.map (,Nothing) . identifiers
    , bottom = const Set.empty
    , latticeLess = Set.isSubsetOf
    , latticeJoin = Set.union
    , transfer = rdTransfer
    }

--- Available expressions ---

type AEEntry = AExp

aeTransfer :: CFG -> Set AEEntry -> Label -> Set AEEntry
aeTransfer cfg old l = (old Set.\\ kill) <> gen
  where
    Just block = Map.lookup l $ _blocks cfg
    gen = allAExp block
    kill = Set.filter (not . (`Set.disjoint` killSet) . occursIn) old
      where
        killSet = defines block

ae :: MonotoneFramework AEEntry
ae =
  MF
    { extremal = const (Set.singleton 0)
    , init = const Set.empty
    , bottom = foldMap allAExp . _blocks
    , latticeLess = flip Set.isSubsetOf
    , latticeJoin = Set.intersection
    , transfer = aeTransfer
    }

-- worklist :: Ord a => MonotoneFramework a -> CFG -> LabelMap (a, a)
worklist :: MonotoneFramework a -> CFG -> IntMap (Set a, Set a)
worklist MF{..} cfg = result $ go (allEdges cfg) initialMap
  where
    initialMap = Map.singleton 0 (init cfg)
    result = Map.mapWithKey (\l pre -> (pre, transfer cfg pre l))
    go [] !output = output
    go ((l, l') : rest) !output =
      let ana_pre = Map.lookup l output ?: bottom cfg
          ana_post = Map.lookup l' output ?: bottom cfg
          new = transfer cfg ana_pre l
          newset = latticeJoin new ana_post
          output' = Map.insert l' newset output
          edges = filter ((== l') . fst) $ allEdges cfg
       in if latticeLess new ana_post
            then go rest output
            else go (edges ++ rest) output'

present :: Show a => IntMap (Set a, Set a) -> IO ()
present = traverse_ f . Map.toList
  where
    f (l, (a, b)) = putStrLn $ show l ++ ": " ++ show (Set.toList a) ++ " " ++ show (Set.toList b)

--- Main ---

-- [y:=x]1; [z:=1]2; while [y>1]3 do ([z:=z*y]4; [y:=y-1]5); [y:=0]6
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

main :: IO ()
main = do
  let cfg = controlFlowGraph factorial
  -- mapM_ print $ Map.toList . Map.map Set.toList $ worklist rd cfg
  present $ worklist ae cfg

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
