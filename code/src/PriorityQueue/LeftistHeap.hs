module PriorityQueue.LeftistHeap where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ type Nat = {v : Int | v >= 0} @-}

data Heap a = Empty | Node {value :: a, left :: (Heap a), right :: (Heap a), rank :: Int}
  deriving (Show)

{-@ data Heap [size] a = Empty
            | Node { value :: a
                    , left  :: {h : Heap a | isLowerBound value h}
                    , right :: {v : Heap a  | isLowerBound value v && rrank v <= rrank left }
                    , rank :: {r : Nat | r == 1 + rrank right}
                  }
 @-}

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

{-@ measure isEmpty @-}
{-@ isEmpty :: Heap a -> Bool @-}
isEmpty :: Heap a -> Bool
isEmpty Empty = True
isEmpty _ = False

{-@ measure findMin @-}
{-@ findMin :: h : { h : Heap a | not isEmpty h} -> {v : a | isLowerBound v h} @-}
findMin :: (Ord a) => Heap a -> a
findMin (Node x l r rank) = x

{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => a -> h : Heap a -> Bool @-}
isLowerBound :: (Ord a) => a -> Heap a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Node x l r _) = v <= x && isLowerBound v l && isLowerBound v r

-- Merge two heaps
{-@ reflect merge @-}
{-@ merge :: h1 : Heap a -> h2: Heap a -> { h : Heap a | (not (isEmpty h1) && not (isEmpty h2)) => isLowerBound (min (findMin h1) (findMin h2)) h } / [size h1, size h2, 0] @-}
merge :: (Ord a) => Heap a -> Heap a -> Heap a
merge Empty Empty = Empty
merge Empty h2@(Node _ _ _ _) = h2
merge h1@(Node _ _ _ _) Empty = h1
merge h1@(Node x1 l1 r1 _) h2@(Node x2 l2 r2 _)
  | x1 <= x2 = makeNode x1 l1 ((merge r1 h2) `withProof` lemma_merge_case1 x1 x2 r1 h2)
  | otherwise = makeNode x2 l2 ((merge h1 r2) `withProof` lemma_merge_case2 x2 x1 r2 h1)

insert :: (Ord a) => a -> Heap a -> Heap a
insert x h = merge (Node x Empty Empty 1) h

-- Transitivity lemma for isLowerBound
{-@ lemma_isLowerBound_transitive :: x : a -> y : {v : a | x <= v} -> h : {h : Heap a | isLowerBound y h} -> {isLowerBound x h} @-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> Heap a -> Proof
lemma_isLowerBound_transitive x y Empty = ()
lemma_isLowerBound_transitive x y (Node z l r _) = lemma_isLowerBound_transitive x y l &&& lemma_isLowerBound_transitive x y r *** QED

{-@ lemma_merge_case1 :: x1 : a  -> x2 : { v : a |  x1  <= v}-> r1 : {h : Heap a | isLowerBound x1 h} -> h2 : {h : Heap a | not (isEmpty h) && isLowerBound x2 h}  -> {isLowerBound x1 (merge r1 h2)} / [size r1, size h2 , 1]@-}
lemma_merge_case1 :: (Ord a) => a -> a -> Heap a -> Heap a -> Proof
lemma_merge_case1 x1 x2 Empty h2 =
  isLowerBound x1 (merge Empty h2)
    ? lemma_isLowerBound_transitive x1 x2 h2
    *** QED
lemma_merge_case1 x1 x2 r1@(Node _ _ _ _) h2@(Node _ _ _ _) =
  isLowerBound x1 (merged)
    ? (lemma_isLowerBound_transitive x1 (min (findMin r1) (findMin h2)) (merged))
    *** QED
 where
  merged = merge r1 h2

{-@ lemma_merge_case2 :: x2 : a -> x1 : { v : a |  x2  <= v} -> r1 : {h : Heap a | isLowerBound x2 h} -> h2 : {h : Heap a | not (isEmpty h) && isLowerBound x1 h}  -> {isLowerBound x2 (merge h2 r1)} / [size h2 , size r1, 1] @-}
lemma_merge_case2 :: (Ord a) => a -> a -> Heap a -> Heap a -> Proof
lemma_merge_case2 x2 x1 Empty h2 =
  isLowerBound x2 (merge Empty h2)
    === isLowerBound x2 h2
    ? lemma_isLowerBound_transitive x2 x1 h2
    *** QED
lemma_merge_case2 x2 x1 h1 Empty = ()
lemma_merge_case2 x2 x1 r1@(Node _ _ _ _) h2@(Node _ _ _ _) =
  isLowerBound x2 (merged)
    ? (lemma_isLowerBound_transitive x2 (min (findMin h2) (findMin r1)) (merged))
    *** QED
 where
  merged = merge h2 r1
