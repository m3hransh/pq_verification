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
