module PriorityQueue.LeftistHeap (PriorityQueue (..), MinView (..), lemma_merge_case1, LeftistHeap (..), isLowerBound) where

import Language.Haskell.Liquid.ProofCombinators

import qualified Language.Haskell.Liquid.Bag as B
import PriorityQueue.Base
import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

data LeftistHeap a = EmptyHeap | HeapNode {value :: a, left :: (LeftistHeap a), right :: (LeftistHeap a), rank :: Int}
  deriving (Show, Eq)

{-@ type LeftistHeapBound a X = { h : LeftistHeap a | isLowerBound X h} @-}
{-@ data LeftistHeap a = EmptyHeap
      | HeapNode { value :: a
         , left  :: LeftistHeapBound a value
         , right :: {v : LeftistHeapBound a value  | rrank v <= rrank left }
         , rank :: {r : Nat | r == 1 + rrank right}
        }
@-}

{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ measure size @-}
{-@ size :: LeftistHeap a -> Nat @-}
size :: LeftistHeap a -> Int
size EmptyHeap = 0
size (HeapNode _ l r _) = 1 + size l + size r

{-@ reflect bag @-}
{-@ bag :: Ord a => LeftistHeap a -> Bag a @-}
bag :: (Ord a) => LeftistHeap a -> B.Bag a
bag EmptyHeap = B.empty
bag (HeapNode x l r _) = B.put x (B.union (bag l) (bag r))

{-@ measure rrank @-}
{-@ rrank :: LeftistHeap a -> Nat @-}
rrank :: LeftistHeap a -> Int
rrank EmptyHeap = 0
rrank h@(HeapNode _ _ _ r) = r

{-@ reflect bagSingleton @-}
{-@ bagSingleton :: x : a -> b: { Bag a | b = B.put x (B.empty)} @-}
bagSingleton :: (Ord a) => a -> B.Bag a
bagSingleton x = B.put x B.empty

{-@ reflect min @-}
{-@ min :: x : a -> y : a -> {v : a |  v <= x && v <= y} @-}
min :: (Ord a) => a -> a -> a
min x y
  | x < y = x
  | otherwise = y

{-@ reflect makeHeapNode @-}
{-@ makeHeapNode :: x : a -> {h : LeftistHeap a | isLowerBound x h} -> {h : LeftistHeap a | isLowerBound x h} -> {h : LeftistHeap a | isLowerBound x h}@-}
makeHeapNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeHeapNode x h1 h2
  | rrank h1 >= rrank h2 = HeapNode x h1 h2 (rrank h2 + 1)
  | otherwise = HeapNode x h2 h1 (rrank h1 + 1)

{-@ measure heapIsEmpty @-}
{-@ heapIsEmpty :: LeftistHeap a -> Bool @-}
heapIsEmpty :: (Ord a) => LeftistHeap a -> Bool
heapIsEmpty EmptyHeap = True
heapIsEmpty _ = False

{-@ measure heapFindMin @-}
{-@ heapFindMin :: h : { h : LeftistHeap a | not heapIsEmpty h } -> {v : a | isLowerBound v h} @-}
heapFindMin :: (Ord a) => LeftistHeap a -> a
heapFindMin (HeapNode x l r rank) = x

{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => a -> h : LeftistHeap a -> Bool @-}
isLowerBound :: (Ord a) => a -> LeftistHeap a -> Bool
isLowerBound _ EmptyHeap = True
isLowerBound v (HeapNode x l r _) = v <= x && isLowerBound v l && isLowerBound v r

{-@ predicate HeapMergeMin H1 H2 H = ((not (heapIsEmpty H1) && not (heapIsEmpty H2)) => isLowerBound (min (heapFindMin H1) (heapFindMin H2)) H ) @-}
{-@ predicate BagUnion H1 H2 H = (bag H == B.union (bag H1) (bag H2)) @-}

{-@ bogusUnion :: {v: ()| not BagUnion (HeapNode 1 EmptyHeap EmptyHeap 1) (HeapNode 1 EmptyHeap EmptyHeap 1) (HeapNode 1 EmptyHeap (HeapNode 2 EmptyHeap EmptyHeap 1) 1)} @-}
bogusUnion :: ()
bogusUnion = ()

-- heapMerge two heaps
{-@ reflect heapMerge @-}
{-@ heapMerge :: h1 : LeftistHeap a
                -> h2: LeftistHeap a
                -> { h : LeftistHeap a | (HeapMergeMin h1 h2 h) && (BagUnion h1 h2 h) }
                / [size h1, size h2, 0]
@-}
heapMerge :: (Ord a) => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
heapMerge EmptyHeap EmptyHeap = EmptyHeap
heapMerge EmptyHeap h2@(HeapNode _ _ _ _) = h2
heapMerge h1@(HeapNode _ _ _ _) EmptyHeap = h1
heapMerge h1@(HeapNode x1 l1 r1 _) h2@(HeapNode x2 l2 r2 _)
  | x1 <= x2 = makeHeapNode x1 l1 ((heapMerge r1 h2) `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeHeapNode x2 l2 ((heapMerge h1 r2) `withProof` lemma_heapMerge_case2 x2 x1 r2 h1)

-- Transitivity lemma for isLowerBound
{-@ lemma_isLowerBound_transitive :: x : a
      -> y : {v : a | x <= v}
      -> h : {h : LeftistHeap a | isLowerBound y h}
      -> {isLowerBound x h}
@-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> LeftistHeap a -> Proof
lemma_isLowerBound_transitive x y EmptyHeap = ()
lemma_isLowerBound_transitive x y (HeapNode z l r _) = lemma_isLowerBound_transitive x y l &&& lemma_isLowerBound_transitive x y r *** QED

{-@ lemma_merge_case1 :: x1 : a
                      -> x2 : {a |  x1  <= x2}
                      -> r1 : LeftistHeapBound a x1
                      -> h2 : {LeftistHeapBound a x2 | not (heapIsEmpty h2)}
                      -> {isLowerBound x1 (heapMerge r1 h2)}
                      / [size r1, size h2, 1]
@-}
lemma_merge_case1 :: (Ord a) => a -> a -> LeftistHeap a -> LeftistHeap a -> Proof
lemma_merge_case1 x1 x2 EmptyHeap h2 =
  isLowerBound x1 (heapMerge EmptyHeap h2)
    ? lemma_isLowerBound_transitive x1 x2 h2
    *** QED
lemma_merge_case1 x1 x2 r1@(HeapNode _ _ _ _) h2@(HeapNode _ _ _ _) =
  isLowerBound x1 (heapMerged)
    ? (lemma_isLowerBound_transitive x1 (min (heapFindMin r1) (heapFindMin h2)) (heapMerged))
    *** QED
 where
  heapMerged = heapMerge r1 h2

{-@ lemma_heapMerge_case2 :: x2 : a
                          -> x1 : { v : a |  x2  <= v}
                          -> r1 : {h : LeftistHeap a | isLowerBound x2 h}
                          -> h2 : {h : LeftistHeap a | not (heapIsEmpty h) && isLowerBound x1 h}
                          -> {isLowerBound x2 (heapMerge h2 r1)} / [size h2 , size r1, 1]
@-}
lemma_heapMerge_case2 :: (Ord a) => a -> a -> LeftistHeap a -> LeftistHeap a -> Proof
lemma_heapMerge_case2 x2 x1 EmptyHeap h2 =
  isLowerBound x2 (heapMerge EmptyHeap h2)
    === isLowerBound x2 h2
    ? lemma_isLowerBound_transitive x2 x1 h2
    *** QED
lemma_heapMerge_case2 x2 x1 h1 EmptyHeap = ()
lemma_heapMerge_case2 x2 x1 r1@(HeapNode _ _ _ _) h2@(HeapNode _ _ _ _) =
  isLowerBound x2 (heapMerged)
    ? (lemma_isLowerBound_transitive x2 (min (heapFindMin h2) (heapFindMin r1)) (heapMerged))
    *** QED
 where
  heapMerged = heapMerge h2 r1

{-@ heapInsert :: x : a
                -> h1 : LeftistHeap a
                -> {h : LeftistHeap a |
                      not (heapIsEmpty h1) => isLowerBound (min x (heapFindMin h1)) h
                      && bag h = B.put x (bag h1) }
@-}
heapInsert :: (Ord a) => a -> LeftistHeap a -> LeftistHeap a
heapInsert x h = heapMerge (HeapNode x EmptyHeap EmptyHeap 1) h

heapDeleteMin :: (Ord a) => LeftistHeap a -> LeftistHeap a
heapDeleteMin EmptyHeap = EmptyHeap
heapDeleteMin h@(HeapNode _ l r _) = heapMerge l r

{-@ reflect isEmptyView @-}
{-@  isEmptyView :: MinView q a -> Bool @-}
isEmptyView :: MinView q a -> Bool
isEmptyView EmptyView = True
isEmptyView (Min _ _) = False

{-@ reflect getMinValue @-}
{-@ getMinValue :: m: { MinView q a| not isEmptyView m} -> a @-}
getMinValue :: MinView q a -> a
getMinValue (Min x _) = x

{-@ reflect getRestHeap @-}
{-@ getRestHeap :: m: { MinView q a| not isEmptyView m} -> q a @-}
getRestHeap :: MinView q a -> q a
getRestHeap (Min _ h) = h

{-@ predicate SplitOK H S = (heapIsEmpty H => isEmptyView S)
                            && (not (heapIsEmpty H) => not (isEmptyView S)
                            && getMinValue S == heapFindMin H
                            && bag H == B.put (getMinValue S) (bag (getRestHeap S)))
@-}

{-@ heapSplit :: h:LeftistHeap a -> { s:MinView LeftistHeap a | SplitOK h s }
@-}
heapSplit :: (Ord a) => LeftistHeap a -> MinView LeftistHeap a
heapSplit EmptyHeap = EmptyView
heapSplit (HeapNode x l r _) = Min x (heapMerge l r)

safeHeapFindMin :: (Ord a) => LeftistHeap a -> Maybe a
safeHeapFindMin EmptyHeap = Nothing
safeHeapFindMin (HeapNode x _ _ _) = Just x

instance PriorityQueue LeftistHeap where
  empty = EmptyHeap
  findMin = safeHeapFindMin
  isEmpty = heapIsEmpty
  merge = heapMerge
  insert = heapInsert
  splitMin = heapSplit
