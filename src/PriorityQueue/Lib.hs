module PriorityQueue.Lib where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

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
{-@ min :: x: a -> y: {v: a | x <= v} -> {v: a | x <= v} @-}
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
{-@ merge :: h1: Heap a -> h2: Heap a ->  { h: Heap a | (not (isEmpty h1) && not (isEmpty h2)) => isLowerBound (min (findMin h1) (findMin h2)) h } @-}
merge :: (Ord a) => Heap a -> Heap a -> Heap a
merge Empty Empty = Empty
merge Empty h2@(Node _ _ _ _) = h2
merge h1@(Node _ _ _ _) Empty = h1
merge h1@(Node x1 l1 r1 _) h2@(Node x2 l2 r2 _)
  | x1 <= x2 = makeNode x1 l1 (merge r1 h2) `withProof` lemma_merge_min_case1 x1 l1 r1 h2 x2
  | otherwise = makeNode x2 l2 (merge h1 r2) `withProof` lemma_merge_min_case2 h1 x2 l2 r2

-- Transitivity lemma for isLowerBound
{-@ lemma_isLowerBound_transitive :: x:a -> y:{v:a | x <= v} -> h:Heap a -> {isLowerBound y h => isLowerBound x h} @-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> Heap a -> Proof
lemma_isLowerBound_transitive x y Empty = ()
lemma_isLowerBound_transitive x y (Node z l r _) = lemma_isLowerBound_transitive x y l &&& lemma_isLowerBound_transitive x y r *** QED

{-@ assume lemma_merge_min_case1 ::  x1:a -> l1:{h:Heap a | isLowerBound x1 h} -> r1:{h:Heap a | isLowerBound x1 h} -> h2:{h:Heap a | not isEmpty h2} -> x2:{v:a | v == findMin h2 && x1  <= v} -> {isLowerBound x1 (merge r1 h2)} @-}
lemma_merge_min_case1 :: (Ord a) => a -> Heap a -> Heap a -> Heap a -> a -> Proof
lemma_merge_min_case1 x1 l1 r1 h2 x2 = ()

{-@ assume lemma_merge_min_case2 :: h1:{h:Heap a | not isEmpty h1} -> x2:a -> l2:{h:Heap a | isLowerBound x2 h} -> r2:{h:Heap a | isLowerBound x2 h} -> {isLowerBound x2 (merge h1 r2)} @-}
lemma_merge_min_case2 :: (Ord a) => Heap a -> a -> Heap a -> Heap a -> Proof
lemma_merge_min_case2 _ _ _ _ = ()

-- Helper lemma for merg
-- -- Helper lemma for merge
{-@ lemma_merge_preserves_min :: x:a -> h1:{h:Heap a | isLowerBound x h} -> h2: {h:Heap a | isLowerBound x h}  -> {isLowerBound x (merge h1 h2)} @-}
lemma_merge_preserves_min :: (Ord a) => a -> Heap a -> Heap a -> Proof
lemma_merge_preserves_min _ Empty Empty = () -- Trivial case: merging two empty heaps
lemma_merge_preserves_min x Empty h2 = ()
lemma_merge_preserves_min x h1 Empty = () -- Trivial case: merging h1 with Empty just returns h1
lemma_merge_preserves_min x h1@(Node x1 l1 r1 _) h2@(Node x2 l2 r2 _)
  | x1 <= x2 =
      -- When merging with x1 <= x2, we create a node with x1 as root and merge r1 with h2
      -- Need to prove: x is a lower bound for makeNode x1 l1 (merge r1 h2)

      -- First, recursively prove that x is a lower bound for merge r1 h2
      lemma_merge_preserves_min x r1 h2
  -- By assumption, x is a lower bound for h1, which includes x1 and l1
  -- x <= x1 holds because x is a lower bound for h1
  -- x is a lower bound for l1 by assumption
  -- x is a lower bound for merge r1 h2 by recursive proof
  -- Therefore, x is a lower bound for makeNode x1 l1 (merge r1 h2)

  | otherwise =
      -- When merging with x1 > x2, we create a node with x2 as root and merge h1 with r2
      -- Need to prove: x is a lower bound for makeNode x2 l2 (merge h1 r2)

      -- First, recursively prove that x is a lower bound for merge h1 r2
      lemma_merge_preserves_min x h1 r2
