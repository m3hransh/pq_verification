module PriorityQueue.BionomialHeap where

import Prelude hiding (sum)

class (Eq a, Show a) => BinaryDigit a where
  sum :: a -> a -> a
  carry :: a -> a -> a
  zero :: a
  one :: a

halfAdder :: (BinaryDigit a) => a -> a -> (a, a)
halfAdder x y = (sum x y, carry x y)

fullAdder :: (BinaryDigit a) => a -> a -> a -> (a, a)
fullAdder x y c =
  let (s1, c1) = halfAdder x y
      (s2, c2) = halfAdder s1 c
   in (s2, sum c1 c2)

add :: (BinaryDigit a, Show a) => [a] -> [a] -> [a]
add x y = addWithCarry x y zero

addWithCarry :: (BinaryDigit a) => [a] -> [a] -> a -> [a]
addWithCarry [] [] c = if c == zero then [] else [c]
addWithCarry xs [] c = addDigit xs c
addWithCarry [] ys c = addDigit ys c
addWithCarry (x : xs) (y : ys) c =
  let (s, c') = fullAdder x y c
   in s : addWithCarry xs ys c'

addDigit :: (BinaryDigit a) => [a] -> a -> [a]
addDigit [] c | c == zero = []
addDigit [] c = [c]
addDigit (x : xs) c = s : addDigit xs c'
 where
  (s, c') = halfAdder x c

instance BinaryDigit Int where
  sum x y = (x + y) `mod` 2
  carry x y = x + y `div` 2
  zero = 0
  one = 1

data MinView q a = Min a (q a) | EmptyView
  deriving (Show)

class PriorityQueue q where
  empty :: q a
  singleton :: (Ord a) => a -> q a
  isEmpty :: q a -> Bool
  merge :: (Ord a) => q a -> q a -> q a
  splitMin :: (Ord a) => q a -> MinView q a
  insert :: (Ord a) => a -> q a -> q a
  insert x q = merge (singleton x) q

data BinTree a = Empty | Node {value :: a, left :: BinTree a, right :: BinTree a}
  deriving (Show)

newtype ToppedTree a = ToppedTree (MinView BinTree a)
  deriving (Show)

instance PriorityQueue ToppedTree where
  empty = ToppedTree EmptyView
  singleton x = ToppedTree (Min x Empty)
  isEmpty (ToppedTree EmptyView) = True
  isEmpty _ = False
  merge (ToppedTree EmptyView) (ToppedTree EmptyView) = ToppedTree EmptyView
  merge (ToppedTree EmptyView) (ToppedTree (Min x2 t2)) = ToppedTree (Min x2 t2)
  merge (ToppedTree (Min x1 t1)) (ToppedTree EmptyView) = ToppedTree (Min x1 t1)
  merge (ToppedTree (Min x1 t1)) (ToppedTree (Min x2 t2))
    | x1 <= x2 = ToppedTree (Min x1 (Node x2 t2 t1))
    | otherwise = ToppedTree (Min x2 (Node x1 t1 t2))

  splitMin (ToppedTree EmptyView) = EmptyView
  splitMin (ToppedTree (Min x bt)) = Min x (secondMin bt)
   where
    secondMin Empty = ToppedTree EmptyView
    secondMin (Node y l r) = merge (ToppedTree (Min y l)) (secondMin r)
