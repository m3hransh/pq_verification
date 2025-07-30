module PriorityQueue.LeftistHeap where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

data Heap a = Empty | Node {value :: a, left :: (Heap a), right :: (Heap a), rank :: Int}
  deriving (Show)

{-@ data Heap a = Empty
      | Node { value :: a
         , left  :: {h : Heap a | isLowerBound value h}
         , right :: {v : Heap a  | isLowerBound value v
                    && rrank v <= rrank left }
         , rank :: {r : Nat | r == 1 + rrank right}
        }
 @-}

{-@ data MinView q a =
        EmptyView
      | Min { minValue :: a, restHeap :: q a }
  @-}
data MinView q a = EmptyView | Min {minValue :: a, restHeap :: q a}

{-@ measure size @-}
{-@ size :: Heap a -> Nat @-}
size :: Heap a -> Int
size Empty = 0
size (Node _ l r _) = 1 + size l + size r

{-@ measure rrank @-}
{-@ rrank :: Heap a -> Nat @-}
rrank :: Heap a -> Int
rrank Empty = 0
rrank h@(Node _ _ _ r) = r

{-@ reflect min @-}
{-@ min :: x : a -> y : a -> {v : a |  v <= x && v <= y} @-}
min :: (Ord a) => a -> a -> a
min x y
  | x < y = x
  | otherwise = y

{-@ reflect makeNode @-}
{-@ makeNode :: x : a -> {h : Heap a| isLowerBound x h} -> {h : Heap a | isLowerBound x h} -> {h : Heap a | isLowerBound x h}@-}
makeNode :: a -> Heap a -> Heap a -> Heap a
makeNode x h1 h2
  | rrank h1 >= rrank h2 = Node x h1 h2 (rrank h2 + 1)
  | otherwise = Node x h2 h1 (rrank h1 + 1)

{-@ measure heapIsEmpty @-}
{-@ heapIsEmpty :: Heap a -> Bool @-}
heapIsEmpty :: (Ord a) => Heap a -> Bool
heapIsEmpty Empty = True
heapIsEmpty _ = False

{-@ measure heapFindMin @-}
{-@ heapFindMin :: h : { h : Heap a | not heapIsEmpty h } -> {v : a | isLowerBound v h} @-}
heapFindMin :: (Ord a) => Heap a -> a
heapFindMin (Node x l r rank) = x

{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => a -> h : Heap a -> Bool @-}
isLowerBound :: (Ord a) => a -> Heap a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Node x l r _) = v <= x && isLowerBound v l && isLowerBound v r

-- heapMerge two heaps
{-@ reflect heapMerge @-}
{-@ heapMerge :: h1 : Heap a -> h2: Heap a -> { h : Heap a | (not (heapIsEmpty h1) && not (heapIsEmpty h2)) => isLowerBound (min (heapFindMin h1) (heapFindMin h2)) h } / [size h1, size h2, 0] @-}
heapMerge :: (Ord a) => Heap a -> Heap a -> Heap a
heapMerge Empty Empty = Empty
heapMerge Empty h2@(Node _ _ _ _) = h2
heapMerge h1@(Node _ _ _ _) Empty = h1
heapMerge h1@(Node x1 l1 r1 _) h2@(Node x2 l2 r2 _)
  | x1 <= x2 = makeNode x1 l1 ((heapMerge r1 h2) `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeNode x2 l2 ((heapMerge h1 r2) `withProof` lemma_heapMerge_case2 x2 x1 r2 h1)

-- Transitivity lemma for isLowerBound
{-@ lemma_isLowerBound_transitive :: x : a -> y : {v : a | x <= v} -> h : {h : Heap a | isLowerBound y h} -> {isLowerBound x h} @-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> Heap a -> Proof
lemma_isLowerBound_transitive x y Empty = ()
lemma_isLowerBound_transitive x y (Node z l r _) = lemma_isLowerBound_transitive x y l &&& lemma_isLowerBound_transitive x y r *** QED

{-@ lemma_merge_case1 :: x1 : a  -> x2 : { v : a |  x1  <= v}-> r1 : {h : Heap a | isLowerBound x1 h} -> h2 : {h : Heap a | not (heapIsEmpty h) && isLowerBound x2 h}  -> {isLowerBound x1 (heapMerge r1 h2)} / [size r1, size h2 , 1]@-}
lemma_merge_case1 :: (Ord a) => a -> a -> Heap a -> Heap a -> Proof
lemma_merge_case1 x1 x2 Empty h2 =
  isLowerBound x1 (heapMerge Empty h2)
    ? lemma_isLowerBound_transitive x1 x2 h2
    *** QED
lemma_merge_case1 x1 x2 r1@(Node _ _ _ _) h2@(Node _ _ _ _) =
  isLowerBound x1 (heapMerged)
    ? (lemma_isLowerBound_transitive x1 (min (heapFindMin r1) (heapFindMin h2)) (heapMerged))
    *** QED
 where
  heapMerged = heapMerge r1 h2

{-@ lemma_heapMerge_case2 :: x2 : a -> x1 : { v : a |  x2  <= v} -> r1 : {h : Heap a | isLowerBound x2 h} -> h2 : {h : Heap a | not (heapIsEmpty h) && isLowerBound x1 h}  -> {isLowerBound x2 (heapMerge h2 r1)} / [size h2 , size r1, 1] @-}
lemma_heapMerge_case2 :: (Ord a) => a -> a -> Heap a -> Heap a -> Proof
lemma_heapMerge_case2 x2 x1 Empty h2 =
  isLowerBound x2 (heapMerge Empty h2)
    === isLowerBound x2 h2
    ? lemma_isLowerBound_transitive x2 x1 h2
    *** QED
lemma_heapMerge_case2 x2 x1 h1 Empty = ()
lemma_heapMerge_case2 x2 x1 r1@(Node _ _ _ _) h2@(Node _ _ _ _) =
  isLowerBound x2 (heapMerged)
    ? (lemma_isLowerBound_transitive x2 (min (heapFindMin h2) (heapFindMin r1)) (heapMerged))
    *** QED
 where
  heapMerged = heapMerge h2 r1

heapInsert :: (Ord a) => a -> Heap a -> Heap a
heapInsert x h = heapMerge (Node x Empty Empty 1) h

heapDeleteMin :: (Ord a) => Heap a -> Heap a
heapDeleteMin Empty = Empty
heapDeleteMin h@(Node _ l r _) = heapMerge l r

heapSplit :: (Ord a) => Heap a -> MinView Heap a
heapSplit Empty = EmptyView
heapSplit (Node x l r _) = Min x (heapMerge l r)

class PriorityQueue pq where
  empty :: (Ord a) => pq a
  isEmpty :: (Ord a) => pq a -> Bool
  insert :: (Ord a) => a -> pq a -> pq a
  splitMin :: (Ord a) => pq a -> MinView pq a

instance PriorityQueue Heap where
  empty = Empty
  isEmpty = heapIsEmpty
  insert = heapInsert
  splitMin = heapSplit
