module PriorityQueue.Lib where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}

{-@ type Nat = {v : Int | v >= 0} @-}

{-@ type HeapUpper a X = Heap {v : a | X <= v} @-}

data Heap a = Empty | Node {value :: a, left :: (Heap a), right :: (Heap a), rank :: Int}
  deriving (Show)

{-@ data Heap [size] a = Empty
            | Node { value :: a
                    ,left  :: {h : Heap a | isLowerBound value h}
                    ,right :: {v : Heap a  | isLowerBound value v && rrank v <= rrank left }
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
{-@ min :: x: a -> y: a -> {v: a |  v <= x && v <= y} @-}
min :: (Ord a) => a -> a -> a
min x y
  | x < y = x
  | otherwise = y

{-@ reflect makeNode @-}
{-@ makeNode :: x: a -> {h: Heap a| isLowerBound x h} -> {h: Heap a| isLowerBound x h} -> {h: Heap a| isLowerBound x h}@-}
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
{-@ findMin :: h:{h: Heap a | not isEmpty h} -> {v: a| isLowerBound v h} @-}
findMin :: (Ord a) => Heap a -> a
findMin (Node x l r rank) = x

{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => a -> Heap a -> Bool @-}
isLowerBound :: (Ord a) => a -> Heap a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Node x l r _) = v <= x && isLowerBound v l && isLowerBound v r

-- Merge two heaps
{-@ reflect merge @-}
{-@  merge :: h1: Heap a -> h2: Heap a ->  { h: Heap a | (not (isEmpty h1) && not (isEmpty h2)) => isLowerBound (min (findMin h1) (findMin h2)) h } @-}
merge :: (Ord a) => Heap a -> Heap a -> Heap a
merge Empty Empty = Empty
merge Empty h2@(Node _ _ _ _) = h2
merge h1@(Node _ _ _ _) Empty = h1
merge h1@(Node x1 l1 r1 _) h2@(Node x2 l2 r2 _)
  | x1 <= x2 = makeNode x1 l1 (merge r1 h2) `withProof` lemma_merge_case x1 r1 h2 x2
  | otherwise = makeNode x2 l2 (merge r2 h1) `withProof` lemma_merge_case x2 r2 h1 x1

-- Transitivity lemma for isLowerBound
{-@ lemma_isLowerBound_transitive :: x:a -> y:{v:a | x <= v} -> h: {h : Heap a | isLowerBound y h} -> {isLowerBound x h} @-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> Heap a -> Proof
lemma_isLowerBound_transitive x y Empty = ()
lemma_isLowerBound_transitive x y (Node z l r _) = lemma_isLowerBound_transitive x y l &&& lemma_isLowerBound_transitive x y r *** QED

{-@ lemma_merge_case :: x1:a  -> r1:{h:Heap a | isLowerBound x1 h} -> h2:{h:Heap a | not isEmpty h2} -> x2:{v:a | v == findMin h2 && x1  <= v} -> {isLowerBound x1 (merge r1 h2)} @-}
lemma_merge_case :: (Ord a) => a -> Heap a -> Heap a -> a -> Proof
lemma_merge_case x1 Empty h2 x2 =
  isLowerBound x1 (merge Empty h2)
    === isLowerBound x1 h2
    ? lemma_isLowerBound_transitive x1 x2 h2
    === True
    *** QED
lemma_merge_case x1 r1@(Node _ _ _ _) h2@(Node _ _ _ _) x2 =
  isLowerBound x1 (merge r1 h2)
    ? (isEmpty h2 === False)
    ? (isEmpty r1 === False)
    ? (lemma_isLowerBound_transitive x1 (min (findMin r1) (findMin h2)) (merge r1 h2))
    === True
    *** QED

{-@ lemma_min_transitive :: x: a -> y:{v : a | x <= v} -> z: {v : a | x <= v} -> {x <= (min y z)} @-}
lemma_min_transitive :: (Ord a) => a -> a -> a -> Proof
lemma_min_transitive x y z
  | y <= z = x =<= y =<= min y z *** QED
  | otherwise = ()
