module Example where
import 

import Prelude hiding (lookup, max)
import Language.Haskell.Liquid.ProofCombinators

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

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
-> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] ys zs = ([] ++ ys) ++ zs
=== ys ++ zs
=== [] ++ (ys ++ zs)
*** QED

assoc (x : xs) ys zs = ((x : xs) ++ ys) ++ zs
===  x : (xs ++ ys) ++ zs
=== (x : ((xs ++ ys) ++ zs) ? assoc xs ys zs)
=== (x : xs) ++ (ys ++ zs)
*** QED
