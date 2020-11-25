{-# LANGUAGE NoImplicitPrelude #-}

import qualified Data.Map.Strict as Map
import Relude
import Test.Hspec

--- AST ---

type Program = S

data S
  = S :- S -- Sequence Statements
  | Assignment Assignment
  | If BExp S S
  | While BExp S
  | Skip
  deriving (Show)

type Identifier = String

data Assignment
  = Identifier := AExp -- Assignment
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

-- data ArithmeticOperator = Plus | Minus | Multiply
-- data RelationalOperator = Gt | Lt | Eq
-- data BooleanOperator = And | Or

--- Analysis ---

type CFG = Map Label (Block, Edge)

-- Label to be associated with a block.
-- Labels start at 1 to fit better with the material
type Label = Int

data Edge = Edge Label | Branch Label Label
  deriving (Show)

data Block = AssignmentBlock Assignment | Expression AExp | Conditional BExp
  deriving (Show)

-- data Edge = Edge Label | Branch Label Label
-- edges :: Label -> CFG -> [Label]
-- edges label cfg = case Map.lookup label cfg of
--   Just (Edge l) -> [l]
--   Just (Branch l1 l2) -> [l1, l2]
--   _ -> []

edges :: Label -> CFG -> [Label]
edges label cfg = undefined -- Map.lookup label cfg ?: []

controlFlowGraph :: Program -> CFG
controlFlowGraph = undefined

--- Main ---

-- [y:=x]1; [z:=1]2; while [y>1]3 do ([z:=z*y]4; [y:=y-1]5); [y:=0]6
factorial :: Program
factorial =
  Assignment ("y" := Variable "x")
    :- Assignment ("z" := Number 1)
    :- While
      (BinaryRelational ">" (Variable "y") (Number 1))
      ( Assignment ("z" := BinaryArithmetic "*" (Variable "z") (Variable "y"))
          :- Assignment ("y" := BinaryArithmetic "-" (Variable "y") (Number 1))
      )
    :- Assignment ("y" := Number 0)

main :: IO ()
main = print $ controlFlowGraph factorial

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
