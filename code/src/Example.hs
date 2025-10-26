{-# LANGUAGE FlexibleInstances #-}

module Example (PList (..), PriorityQueue (..), MinView (..), ToppedTree, BinTree (..), add, BinomialHeap) where

import PriorityQueue.Base

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (lookup, max, sum)

{-@ LIQUID "--reflection"      @-}
{-@ fib :: i:Nat -> Int  @-}
fib :: Int -> Int
fib i
  | i == 0 = 0
  | i == 1 = 1
  | otherwise = fib (i - 1) + fib (i - 2)

{-@ range :: lo:Int -> hi:Int -> [Int] / [hi - lo]@-}
range :: Int -> Int -> [Int]
range lo hi
  | lo < hi = lo : range (lo + 1) hi
  | otherwise = []

{-@ lookup :: i:Nat -> xs:{[a] | i < len xs} -> a @-}
lookup :: Int -> [a] -> a
lookup 0 (x : _) = x
lookup x (_ : xs) = lookup (x - 1) (xs)

{-@ x :: {v:Int | v >= 0} @-}
x :: Int
x = 2

{-@ type Nat = {v: Int| v >= 0} @-}

{-@ gcdE :: a:Nat -> {b:Nat | b < a} -> Nat @-}
gcdE :: Int -> Int -> Int
gcdE a 0 = a
gcdE a b = gcdE b (a `mod` b)

-- {-@ mod :: a:Nat -> b:{Nat | b /= 0} -> {v:Nat | v < b} @-}
-- mod :: Int -> Int -> Int
-- mod a b
--   | a < b = a
--   | otherwise = mod (a - b) b

-- data Sparse a = SP {spDim :: Int, spElems :: [(Int, a)]}
--
{-@ max:: forall <p :: Int -> Bool> . Int <p> -> Int<p> -> Int<p> @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ xPos :: {v: _ | v > 0} @-}
xPos :: Int
xPos = max 10 (10)

-- {-@ type Prop = Bool @-}
-- {-@ (.) :: forall < p :: b -> c -> Bool , q :: a -> b -> Bool>. f:(x:b -> c<p x>) -> g: (x:a -> b<q x>) -> y:a ->  c<p (g y)> @-}
-- (.) :: (b -> c) -> (a -> b) -> a -> c
-- (.) f g x = f (g x)
{-@ data PList a <p:: a -> a -> Bool> = Nil | Cons { phd :: a, ptl :: PList <p> a <p phd>} @-}
data PList a = Nil | Cons a (PList a)

{-@ type SortedList = PList <{\x y -> x <= y}> Int @-}

{-@ posList :: PList<{\head v -> (head *  2) == v }> Int @-}
posList :: PList Int
posList = Cons 2 (Cons 4 Nil)

{-@ okSorted :: SortedList @-}
okSorted :: PList Int
okSorted = Cons 2 (Cons 4 Nil)

data Person = P
  { name :: String
  , age :: Int
  }
  deriving (Show, Eq)

map' :: (a -> b) -> PList a -> PList b
map' f Nil = Nil
map' f (Cons x xs) = Cons (f x) (map' f xs)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f Leaf = Leaf
mapTree f (Node x left right) = Node (f x) (mapTree f left) (mapTree f right)

class Functor' f where
  fmap' :: (a -> b) -> f a -> f b

instance Functor' PList where
  fmap' = map'

instance Functor' Tree where
  fmap' = mapTree

agePeoplePlusOne :: (Functor' f) => f Person -> f Person
agePeoplePlusOne col = fmap' (\x -> P (name x) (age x + 1)) col

getAges :: (Functor' f) => f Person -> f Int
getAges col = fmap' age col

instance PriorityQueue PList where
  empty = Nil
  isEmpty Nil = True
  isEmpty _ = False
  insert x xs = Cons x xs
  merge Nil ys = ys
  merge (Cons x xs) ys = Cons x (merge xs ys)
  findMin xs = case splitMin xs of
    EmptyView -> Nothing
    Min v _ -> Just v
  splitMin Nil = EmptyView
  splitMin (Cons x xs) = case splitMin xs of
    EmptyView -> Min x Nil
    Min v rest ->
      if x <= v
        then Min x xs
        else Min v (Cons x rest)

type ToppedTree a = MinView BinTree a
data BinTree a = BLeaf | BNode a (BinTree a) (BinTree a)
  deriving (Show, Eq)

mergeToppedTrees :: (Ord a) => ToppedTree a -> ToppedTree a -> ToppedTree a
mergeToppedTrees EmptyView EmptyView = EmptyView
mergeToppedTrees EmptyView ys@(Min _ _) = ys
mergeToppedTrees xs@(Min _ _) EmptyView = xs
mergeToppedTrees (Min a t) (Min b u) =
  if a <= b
    then Min a (BNode b u t)
    else Min b (BNode a t u)

instance PriorityQueue (MinView BinTree) where
  empty = EmptyView
  isEmpty EmptyView = True
  isEmpty _ = False
  insert x q = merge (Min x BLeaf) q

  merge = mergeToppedTrees

  findMin EmptyView = Nothing
  findMin (Min v _) = Just v
  splitMin EmptyView = EmptyView
  splitMin (Min v rest) = Min v (secondBest rest)
   where
    secondBest BLeaf = EmptyView
    secondBest (BNode x left right) = merge (Min x left) (secondBest right)

class (Eq b) => BinaryDigit b where
  zero :: b
  carry, sum :: b -> b -> b

halfAdder :: (BinaryDigit b) => b -> b -> (b, b)
halfAdder x y = (sum x y, carry x y)

fullAdder :: (BinaryDigit b) => b -> b -> b -> (b, b)
fullAdder x y cin =
  let (s1, c1) = halfAdder x y
      (s2, c2) = halfAdder s1 cin
   in (s2, sum c1 c2)

add :: (BinaryDigit b) => [b] -> [b] -> [b]
add xs ys = addWithCarry xs ys zero

{-@ addWithCarry :: xs:[a] -> ys:[a] -> c:a -> {v:[a] | len v >= len ys} / [len xs, len ys]  @-}
addWithCarry :: (BinaryDigit b) => [b] -> [b] -> b -> [b]
addWithCarry [] [] c
  | c == zero = []
  | otherwise = [c]
addWithCarry (x : xs) [] c
  | c == zero = x : xs
  | otherwise =
      let (s, c') = fullAdder x zero c
       in s : addWithCarry xs [] c'
addWithCarry [] (y : ys) c =
  let (s, c') = fullAdder zero y c
   in s : addWithCarry [] ys c'
addWithCarry (x : xs) (y : ys) c =
  let (s, c') = fullAdder x y c
   in s : addWithCarry xs ys c'

instance BinaryDigit Int where
  zero = 0
  sum x y = (x + y) `mod` 2
  carry x y = if x + y >= 2 then 1 else 0

instance (Ord a) => BinaryDigit (ToppedTree a) where
  zero = EmptyView
  sum EmptyView EmptyView = EmptyView
  sum x@(Min _ _) EmptyView = x
  sum EmptyView x@(Min _ _) = x
  sum x@(Min a t) y@(Min b u) = EmptyView
  carry EmptyView EmptyView = EmptyView
  carry x@(Min _ _) EmptyView = EmptyView
  carry EmptyView y@(Min _ _) = EmptyView
  carry x@(Min a t) y@(Min b u)
    | a <= b = Min a (BNode b u t)
    | otherwise = Min b (BNode a t u)

instance (Ord a) => Ord (ToppedTree a) where
  t <= EmptyView = True
  EmptyView <= t = False
  (Min a _) <= (Min b _) = a <= b

extractMin :: (Ord a) => [ToppedTree a] -> MinView [] (ToppedTree a)
extractMin [] = EmptyView
extractMin (t : ts) = case extractMin ts of
  EmptyView -> Min t []
  Min v rest
    | t <= v -> Min t (EmptyView : ts)
    | otherwise -> Min v (t : rest)

dismantle :: BinTree a -> [ToppedTree a]
dismantle BLeaf = []
dismantle (BNode x left right) = Min x left : dismantle right

newtype BinomialHeap a = BinomialHeap [ToppedTree a]
  deriving (Show, Eq)

instance PriorityQueue BinomialHeap where
  empty = BinomialHeap []
  isEmpty (BinomialHeap []) = True
  isEmpty _ = False
  insert x xs = merge (BinomialHeap [Min x BLeaf]) xs
  merge (BinomialHeap xs) (BinomialHeap ys) = BinomialHeap (add xs ys)
  findMin (BinomialHeap xs) = case extractMin xs of
    EmptyView -> Nothing
    Min EmptyView _ -> Nothing
    Min (Min v _) _ -> Just v
  splitMin (BinomialHeap xs) = case extractMin xs of
    EmptyView -> EmptyView
    Min EmptyView _ -> EmptyView
    Min (Min a b) rest -> Min a (BinomialHeap (add (reverse (dismantle b)) rest))
