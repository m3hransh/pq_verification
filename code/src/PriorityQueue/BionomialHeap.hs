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
isLowerBound v (Bin x l r _) = v <= x && isLowerBound v l && isLowerBound v r

data BinTree a = Empty | Bin {value :: a, left :: BinTree a, right :: BinTree a, height :: Int}
  deriving (Show)

{-@ measure bheight @-}
{-@ bheight :: BinTree a -> Nat @-}
bheight :: BinTree a -> Int
bheight Empty = 0
bheight (Bin _ _ _ h) = h

{-@ data BinTree a = Empty
      | Bin { value :: a
           , left  :: {t : BinTree a | isLowerBound value t}
          , right :: {t : BinTree a | bheight t == bheight left}
          , height :: {h : Nat | bheight left + 1 == h && bheight right + 1 == h}

           }
  @-}
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

{-@ measure tsize @-}
{-@ tsize :: ToppedTree a -> Nat @-}
tsize :: ToppedTree a -> Int
tsize EmptyTree = 0
tsize (WinnerTree _ t) = 1 + bheight t

{-@ singleton :: Ord a => a -> ToppedTree a @-}
singleton :: (Ord a) => a -> ToppedTree a
singleton x = WinnerTree x Empty

{-@ measure isEmpty @-}
{-@ isEmpty :: ToppedTree a -> Bool @-}
isEmpty :: ToppedTree a -> Bool
isEmpty EmptyTree = True
isEmpty _ = False

{-@reflect merge @-}
{-@ merge :: Ord a => t1: {t: ToppedTree a | tsize t> 0} -> t2: {t : ToppedTree a | tsize t == tsize t1} -> {v: ToppedTree a | tsize v == tsize t1 + 1} @-}
merge :: (Ord a) => ToppedTree a -> ToppedTree a -> ToppedTree a
merge (WinnerTree x1 t1) (WinnerTree x2 t2)
  | x1 <= x2 = WinnerTree x1 ((Bin x2 t2 t1 (bheight t1 + 1)) `withProof` lemma_isLowerBound_transitive x1 x2 t2)
  | otherwise = WinnerTree x2 ((Bin x1 t1 t2 (bheight t2 + 1)) `withProof` lemma_isLowerBound_transitive x2 x1 t1)

{-@ lemma_isLowerBound_transitive :: x1 : a -> x2 : {v : a | x1 <= v} ->  t : {v : BinTree a | isLowerBound x2 t } -> {isLowerBound x1 t} @-}
lemma_isLowerBound_transitive :: a -> a -> BinTree a -> Proof
lemma_isLowerBound_transitive x1 x2 Empty = ()
lemma_isLowerBound_transitive x1 x2 (Bin x t1 t2 _) = lemma_isLowerBound_transitive x1 x2 t1 &&& lemma_isLowerBound_transitive x1 x2 t2 *** QED

-- {-@ splitMin :: Ord a => ToppedTree a -> MinView a @-}
-- splitMin :: (Ord a) => ToppedTree a -> MinView a
-- splitMin EmptyTree = EmptyView
-- splitMin (WinnerTree x bt) = Min x (secondMin bt)
--  where
--   {-@ secondMin :: Ord a => BinTree a -> ToppedTree a @-}
--   secondMin :: (Ord a) => BinTree a -> ToppedTree a
--   secondMin Empty = EmptyTree
--   secondMin (Bin y l r _) = merge (WinnerTree y l) (secondMin r)
--
-- {-@ insert :: Ord a => a -> ToppedTree a -> ToppedTree a @-}
-- insert :: (Ord a) => a -> ToppedTree a -> ToppedTree a
-- insert x pq = merge (singleton x) pq

-- Helper function for creating singleton trees
{-@ singletonTree :: Ord a => x:a -> ToppedTree a @-}
singletonTree :: (Ord a) => a -> ToppedTree a
singletonTree x = (WinnerTree x (Empty `withProof` (isLowerBound x Empty)))

-- {-@ type BinBinomialHeap a = [ToppedTree a] <{\hd v -> (tsize hd) < (tsize v) }> @-}
-- type BinBinomialHeap a = [ToppedTree a]
--
-- This is errornous because it does not satisfy the invariant that the size of the first tree is less than the second.
-- I think this is error in Liquid Haskell.
-- btree :: BinBinomialHeap Int
-- btree = [WinnerTree 1 (Bin 3 Empty Empty), EmptyTree]

{-@ data PList a < p :: a -> a -> Bool> =
        Nil
      | Cons { phd :: a, ptl :: PList < p >  a < p phd > }  @-}
data PList a = Nil | Cons a (PList a)

{-@ measure bhsize @-}
{-@ bhsize :: PList a -> Nat @-}
bhsize :: PList a -> Int
bhsize Nil = 0
bhsize (Cons h t) = 1 + bhsize t

{-@ type BionomialHeap a = PList <{\hd v -> (tsize hd) <= (tsize v) }> (ToppedTree a) @-}
type BionomialHeap a = PList (ToppedTree a)

-- Helper functions for BionomialHeap operations

{-@ emptyHeap :: BionomialHeap a @-}
emptyHeap :: BionomialHeap a
emptyHeap = Nil

{-@ isEmptyHeap :: BionomialHeap a -> Bool @-}
isEmptyHeap :: BionomialHeap a -> Bool
isEmptyHeap Nil = True
isEmptyHeap _ = False

-- Insert a tree into a heap, maintaining size ordering
{-@ reflect insertTree @-}
{-@ insertTree :: Ord a => {t : ToppedTree a | tsize t > 0}  -> h : BionomialHeap a -> BionomialHeap a  / [bhsize h] @-}
insertTree :: (Ord a) => ToppedTree a -> BionomialHeap a -> BionomialHeap a
insertTree t Nil = Cons t Nil
insertTree t (Cons h hs)
  | tsize t < tsize h = Cons t (Cons h hs)
  | tsize t == tsize h = insertTree (merge t h) hs
  | otherwise = Cons h (insertTree t hs)

--
-- -- Merge two binomial heaps with termination measure
-- {-@ mergeHeaps :: Ord a => h1:BionomialHeap a -> h2:BionomialHeap a -> BionomialHeap a / [len h1 + len h2] @-}
-- mergeHeaps :: (Ord a) => BionomialHeap a -> BionomialHeap a -> BionomialHeap a
-- mergeHeaps Nil h2 = h2
-- mergeHeaps h1 Nil = h1
-- mergeHeaps (Cons t1 h1) (Cons t2 h2)
--   | tsize t1 < tsize t2 = Cons t1 (mergeHeaps h1 (Cons t2 h2))
--   | tsize t1 > tsize t2 = Cons t2 (mergeHeaps (Cons t1 h1) h2)
--   | otherwise = insertTree (merge t1 t2) (mergeHeaps h1 h2)
--
-- -- Insert a single element into a binomial heap
-- {-@ insertHeap :: Ord a => a -> BionomialHeap a -> BionomialHeap a @-}
-- insertHeap :: (Ord a) => a -> BionomialHeap a -> BionomialHeap a
-- insertHeap x h = insertTree (singleton x) h

-- Helper function to calculate length of PList
{-@ measure len @-}
{-@ len :: PList a -> Nat @-}
len :: PList a -> Int
len Nil = 0
len (Cons _ xs) = 1 + len xs
