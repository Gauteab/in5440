{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedLists #-}
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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

import GHC.Exts
import Control.Lens
import Data.Data (Data)
import Data.Data.Lens (biplate)
import Data.Foldable ( Foldable(foldr1), all, traverse_ )
import qualified Data.IntMap.Strict as Map
import qualified Data.Set as Set
import Relude
import qualified Text.Show

--- AST ---

type Program = S

data S
  = AssignmentStatement Assignment
  | S ::: S -- Sequence Statements
  | Skip
  | If BExp S S
  | While BExp S
  deriving (Show)

infixr 5 :::

newtype Identifier
  = Identifier String
  deriving (Eq, Data, Ord)

instance Show Identifier where show (Identifier s) = s

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

data CFG = CFG
  { _blocks :: IntMap Block
  , _edges :: IntMap [Label]
  }
  deriving (Show, Data)

data Block = AssignmentBlock Assignment | Expression AExp | Conditional BExp
  deriving (Show, Data)

type Flow = [(Label, Label)]

type Label = Int

instance Semigroup CFG where
  (CFG blocks1 edges1) <> (CFG blocks2 edges2) =
    CFG (blocks1 <> blocks2) (Map.unionWith (<>) edges1 edges2)

instance Monoid CFG where
  mempty = CFG mempty mempty

-- makeLenses ''CFG
deriving instance Plated Block
deriving instance Plated CFG

makeGraph :: Label -> [Block] -> [Label] -> CFG
makeGraph label blocks edges =
  CFG
    { _blocks = Map.fromList $ zip (repeat label) blocks
    , _edges = Map.singleton label edges
    }

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
      AssignmentStatement a -> do
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
freshLabel = state $ id &&& (+ 1)

getFlow :: CFG -> Flow
getFlow cfg = do
  (from, vs) <- Map.toList $ _edges cfg
  to <- vs
  pure (from, to)

--- Analysis ---

allBinaryArithmetic :: Data a => a -> Set AExp
allBinaryArithmetic = toSetOf $ biplate . cosmos . filteredBy _BinaryArithmetic

allIdentifiers :: Data a => a -> Set Identifier
allIdentifiers = toSetOf biplate

toSetOf :: Ord a => Getting (Endo [a]) s a -> s -> Set a
toSetOf l = Set.fromList . toListOf l

uses :: Block -> Set Identifier
uses (AssignmentBlock (_ := a)) = allIdentifiers a
uses a = allIdentifiers a

defines :: Block -> Set Identifier
defines (AssignmentBlock (x := _)) = Set.singleton x
defines _ = Set.empty

findExtremal :: Flow -> Set Label
findExtremal edges = Set.fromList . filter (noInEdges edges) . map fst $ edges
  where
    noInEdges :: Flow -> Label -> Bool
    noInEdges edges l = all ((/= l) . snd) edges

--- Monotone Framework ---

data MonotoneFramework a = MF
  { ι :: Set a
  , (⊥) :: Set a
  , (⊑) :: Set a -> Set a -> Bool
  , (⨆) :: Set a -> Set a -> Set a
  , flow :: Flow
  , extremal :: Flow -> Set Label
  , transfer :: Set a -> Label -> Set a
  }

type MFPResult a = IntMap (Set a, Set a)

mfp :: (CFG -> MonotoneFramework a) -> CFG -> MFPResult a
mfp getInstance cfg = result $ solve flow initialMap
  where
    MF{..} = getInstance cfg

    -- Initialization
    initialMap = Map.fromList $ zip (Set.toList $ extremal flow) (repeat ι)

    -- Collecting the result
    result = Map.mapWithKey (\l pre -> (pre, transfer pre l))

    solve [] analysis = analysis
    solve ((l, l') : rest) analysis =
      let analysisPre = Map.lookup l analysis ?: (⊥)
          analysisPost = Map.lookup l' analysis ?: (⊥)
          new = transfer analysisPre l
          jointAnalysis = new ⨆ analysisPost
          analysis' = Map.insert l' jointAnalysis analysis
          newEdges = filter ((== l') . fst) flow
       in if new ⊑ analysisPost
            then solve rest analysis
            else solve (newEdges ++ rest) analysis'

present :: Show a => MFPResult a -> IO ()
present = traverse_ f . Map.toList
  where
    f (l, (a, b)) = putStrLn $ show l ++ ": " ++ show (Set.toList a) ++ " " ++ show (Set.toList b)

--- Reaching definitions ---

data RDEntry = RDEntry {rdIdentifier :: Identifier, rdLabel :: Maybe Label} deriving (Ord, Eq)

rdTransfer :: CFG -> Set RDEntry -> Label -> Set RDEntry
rdTransfer cfg old l = gen <> (old Set.\\ kill)
  where
    block = Map.lookup l (_blocks cfg) ?: error ("Failed to find block at label " <> show l <> " in reaching definitions transfer function")
    gen = Set.map (`RDEntry` Just l) $ defines block
    kill = Set.filter ((`Set.member` killSet) . rdIdentifier) old
    killSet = defines block

rd :: CFG -> MonotoneFramework RDEntry
rd cfg =
  MF
    { extremal = const (Set.singleton 0)
    , ι = Set.map (`RDEntry` Nothing) . allIdentifiers $ cfg
    , (⊥) = Set.empty
    , (⊑) = Set.isSubsetOf
    , (⨆) = Set.union
    , transfer = rdTransfer cfg
    , flow = getFlow cfg
    }

instance Show RDEntry where
  show (RDEntry identifier label) = "(" <> show identifier <> "," <> maybe "?" show label <> ")"

--- Available expressions ---

type AEEntry = AExp

aeTransfer :: CFG -> Set AEEntry -> Label -> Set AEEntry
aeTransfer cfg old l = (old Set.\\ kill) <> gen
  where
    Just block = Map.lookup l $ _blocks cfg
    gen = allBinaryArithmetic block
    kill = Set.filter (not . (`Set.disjoint` killSet) . allIdentifiers) old
      where
        killSet = defines block

ae :: CFG -> MonotoneFramework AEEntry
ae cfg =
  MF
    { extremal = const (Set.singleton 0)
    , ι = Set.empty
    , (⊥) = allBinaryArithmetic cfg
    , (⊑) = flip Set.isSubsetOf
    , (⨆) = Set.intersection
    , transfer = aeTransfer cfg
    , flow = getFlow cfg
    }

-- Very busy expressions

type VBEntry = AExp

vbTransfer :: CFG -> Set VBEntry -> Label -> Set VBEntry
vbTransfer = aeTransfer

vb :: CFG -> MonotoneFramework AEEntry
vb cfg =
  MF
    { extremal = findExtremal
    , ι = Set.empty
    , (⊥) = allBinaryArithmetic cfg
    , (⊑) = flip Set.isSubsetOf
    , (⨆) = Set.intersection
    , transfer = vbTransfer cfg
    , flow = swap <$> getFlow cfg
    }

--- DSL ---

infixl 7 *.
infixl 4 -., +.
infix 4 >., <., ==.
(*.) x y = BinaryArithmetic "*" (toAExp x) (toAExp y)
(-.) x y = BinaryArithmetic "-" (toAExp x) (toAExp y)
(+.) x y = BinaryArithmetic "+" (toAExp x) (toAExp y)
(>.) x y = BinaryRelational ">" (toAExp x) (toAExp y)
(<.) = BinaryRelational "<" (toAExp x) (toAExp y)
(==.) = BinaryRelational "=="

infix 3 =.
(=.) :: ToAExp a => Identifier -> a -> S
i =. x = AssignmentStatement $ i := toAExp x


class ToAExp a where toAExp :: a -> AExp
instance ToAExp Identifier where toAExp = Variable
instance ToAExp AExp where toAExp = id

class ToStatement t where toStatement :: t -> S
instance ToStatement S where toStatement = id
instance ToStatement Assignment where toStatement = AssignmentStatement
instance ToStatement a => ToStatement [a] where
  toStatement [] = Skip
  toStatement xs = foldr1 (:::) $ map toStatement xs

instance IsString Identifier where fromString = Identifier
x, y, z :: Identifier
x = "x"
y = "y"
z = "z"

instance IsList S where
  type Item S = S
  fromList [] = Skip
  fromList xs = foldr1 (:::) xs
  toList = undefined

--- Main ---

-- [y:=x]0; [z:=1]1; while [y>1]2 do ([z:=z*y]3; [y:=y-1]4); [y:=0]5
factorial :: Program
factorial =
    [ y =. x
    , z =. Number 1
    , While
        (y >. Number 1)
        [ z =. z *. y
        , y =. y -. Number 1
        ]
    , y =. Number 0
    ]

factorialCFG :: CFG
factorialCFG = controlFlowGraph factorial

main :: IO ()
main = do
  putStrLn "--- Reaching Definitions ---\n"
  present $ mfp rd factorialCFG
  putStrLn "\n--- Available Expressions ---\n"
  present $ mfp ae factorialCFG
  putStrLn "\n--- Very Busy Expressions ---\n"
  present $ mfp vb factorialCFG

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
