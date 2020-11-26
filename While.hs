{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}

import qualified Data.Map.Strict as Map
import Relude
import Text.Pretty.Simple (pPrint)

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
  deriving (Show)

data BExp
  = True'
  | False'
  | Not BExp
  | BinaryBoolean BooleanOperator BExp BExp
  | BinaryRelational RelationalOperator AExp AExp
  deriving (Show)

type ArithmeticOperator = String
type RelationalOperator = String
type BooleanOperator = String

--- Analysis ---

data CFG = CFG
  { _entries :: Map Label Block
  , _edges :: Map Label [Label]
  }
  deriving (Show)

makeGraph :: Label -> [Block] -> [Label] -> CFG
makeGraph label blocks edges =
  CFG
    { _entries = Map.fromList $ zip (repeat label) blocks
    , _edges = Map.singleton label edges
    }

instance Semigroup CFG where
  (CFG entries1 edges1) <> (CFG entries2 edges2) =
    CFG (entries1 <> entries2) (Map.unionWith (<>) edges1 edges2)

instance Monoid CFG where
  mempty = CFG mempty mempty

type Label = Int

data Block = AssignmentBlock Assignment | Expression AExp | Conditional BExp
  deriving (Show)

controlFlowGraph :: Program -> CFG
controlFlowGraph = flip evalState 1 . f
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
        let entries = Map.singleton label (Conditional condition)
        let edges = Map.fromList [(lastBodyLabel, [label]), (label, [label + 1])]
        pure $ CFG entries edges <> bodyGraph

freshLabel :: State Label Label
freshLabel = state (\n -> (n, n + 1))

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
main = pPrint $ controlFlowGraph factorial

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
