module PriorityQueue.BionomialHeap where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinators (Proof, withProof)
import PriorityQueue.LeftistHeap (lemma_merge_case1)
import Prelude hiding (sum)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Binary tree with heap property
{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => v:a -> t:BinTree a -> Bool @-}
isLowerBound :: (Ord a) => a -> BinTree a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Bin x l r) = v <= x && isLowerBound v l && isLowerBound v r

{-@ data BinTree a = Empty
      | Bin { value :: a
           , left  :: {t : BinTree a | isLowerBound value t}
           , right :: BinTree a
           }
  @-}
data BinTree a = Empty | Bin {value :: a, left :: BinTree a, right :: BinTree a}
  deriving (Show)

-- Priority queue data structure
{-@ data ToppedTree a = EmptyTree
                      | WinnerTree { min :: a
                           , rest :: {rst : BinTree a | isLowerBound min rst}
                           }
  @-}
data ToppedTree a
  = EmptyTree
  | WinnerTree {min :: a, rest :: (BinTree a)}
  deriving (Show)

data MinView a = EmptyView | Min a (ToppedTree a)
  deriving (Show)

{-@ singleton :: Ord a => a -> ToppedTree a @-}
singleton :: (Ord a) => a -> ToppedTree a
singleton x = WinnerTree x Empty

{-@ isEmpty :: ToppedTree a -> Bool @-}
isEmpty :: ToppedTree a -> Bool
isEmpty EmptyTree = True
isEmpty _ = False

{-@ merge :: Ord a => ToppedTree a -> ToppedTree a -> ToppedTree a @-}
merge :: (Ord a) => ToppedTree a -> ToppedTree a -> ToppedTree a
merge EmptyTree EmptyTree = EmptyTree
merge EmptyTree (WinnerTree x2 t2) = WinnerTree x2 t2
merge (WinnerTree x1 t1) EmptyTree = WinnerTree x1 t1
merge (WinnerTree x1 t1) (WinnerTree x2 t2)
  | x1 <= x2 = WinnerTree x1 ((Bin x2 t2 t1) `withProof` lemma_isLowerBound_transitive x1 x2 t2)
  | otherwise = WinnerTree x2 ((Bin x1 t1 t2) `withProof` lemma_isLowerBound_transitive x2 x1 t1)

{-@ lemma_isLowerBound_transitive :: x1 : a -> x2 : {v : a | x1 <= v} ->  t : {v : BinTree a | isLowerBound x2 t } -> {isLowerBound x1 t} @-}
lemma_isLowerBound_transitive :: a -> a -> BinTree a -> Proof
lemma_isLowerBound_transitive x1 x2 Empty = ()
lemma_isLowerBound_transitive x1 x2 (Bin x t1 t2) = lemma_isLowerBound_transitive x1 x2 t1 &&& lemma_isLowerBound_transitive x1 x2 t2 *** QED

{-@ splitMin :: Ord a => ToppedTree a -> MinView a @-}
splitMin :: (Ord a) => ToppedTree a -> MinView a
splitMin EmptyTree = EmptyView
splitMin (WinnerTree x bt) = Min x (secondMin bt)
 where
  {-@ secondMin :: Ord a => BinTree a -> ToppedTree a @-}
  secondMin :: (Ord a) => BinTree a -> ToppedTree a
  secondMin Empty = EmptyTree
  secondMin (Bin y l r) = merge (WinnerTree y l) (secondMin r)

{-@ insert :: Ord a => a -> ToppedTree a -> ToppedTree a @-}
insert :: (Ord a) => a -> ToppedTree a -> ToppedTree a
insert x pq = merge (singleton x) pq

-- Helper function for creating singleton trees
{-@ singletonTree :: Ord a => x:a -> ToppedTree a @-}
singletonTree :: (Ord a) => a -> ToppedTree a
singletonTree x = (WinnerTree x (Empty `withProof` (isLowerBound x Empty)))
