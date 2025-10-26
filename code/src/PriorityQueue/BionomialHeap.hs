module PriorityQueue.BionomialHeap where

import Control.Arrow (Arrow (second))
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (max, sum)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect max @-}
{-@ max:: forall <p :: Int -> Bool> . Int <p> -> Int<p> -> Int<p> @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

-- Binary tree with heap property
{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => v:a -> t:BinTree a -> Bool @-}
isLowerBound :: (Ord a) => a -> BinTree a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Bin x l r _) = v <= x && isLowerBound v l && isLowerBound v r

{-@ lemma_isLowerBound_transitive :: x:a -> y:{a | x <= y} -> t:{BinTree a | isLowerBound y t} -> {isLowerBound x t} @-}
lemma_isLowerBound_transitive :: (Ord a) => a -> a -> BinTree a -> Proof
lemma_isLowerBound_transitive x y Empty = ()
lemma_isLowerBound_transitive x y (Bin z l r _) =
  lemma_isLowerBound_transitive x y l
    &&& lemma_isLowerBound_transitive x y r

{-@ type BinTreeHeight a H = { t : BinTree a | bheight t == H } @-}

{-@ type BinTreeBound a X = {b : BinTree a | isLowerBound X b} @-}
{-@ data BinTree a = Empty
      | Bin { value :: a
          ,left  :: BinTreeBound a value
          ,right :: BinTreeHeight a (bheight left)
          ,height :: {h : Nat | h == 1 + bheight right}
           }
  @-}
data BinTree a
  = Empty
  | Bin
      { value :: a
      , left :: BinTree a
      , right :: BinTree a
      , height :: Int
      }
  deriving (Show, Eq)

{-@ measure bheight @-}
{-@ bheight :: BinTree a -> Nat @-}
bheight :: BinTree a -> Int
bheight Empty = 0
bheight (Bin _ _ _ h) = h

b :: BinTree Int
b = Bin 2 (Bin 3 Empty Empty 1) (Bin 4 Empty Empty 1) 2

{-@ data Pennant a = P { root :: a
           ,size  :: Nat
           ,bin   :: {b : BinTreeBound a root | bheight b == size}
           }
  @-}
data Pennant a = P {root :: a, size :: Int, bin :: (BinTree a)}
  deriving (Show, Eq)

pennantExample :: Pennant Int
pennantExample = P 3 2 (Bin 4 (Bin 7 Empty Empty 1) (Bin 3 Empty Empty 1) 2)

{-@ measure psize @-}
{-@ psize :: Pennant a -> Nat @-}
psize :: Pennant a -> Int
psize (P _ s _) = s

{-@ singleton :: Ord a => a -> {v:Pennant a | psize v == 0} @-}
singleton :: (Ord a) => a -> Pennant a
singleton x = P x 0 Empty

{-@ measure isEmpty @-}
{-@ isEmpty :: Pennant a -> Bool @-}
isEmpty :: Pennant a -> Bool
isEmpty _ = False

{-@reflect merge @-}
{-@ merge :: Ord a => t1: Pennant a -> t2: {t : Pennant a | psize t == psize t1} -> {v: Pennant a| psize v == psize t1 + 1 } @-}
merge :: (Ord a) => Pennant a -> Pennant a -> Pennant a
merge (P x1 s1 t1) (P x2 s2 t2)
  | x1 <= x2 = (P x1 (s1 + 1) ((Bin x2 t2 t1 (bheight t1 + 1)) `withProof` (lemma_isLowerBound_transitive x1 x2 t2)))
  | otherwise = (P x2 (s1 + 1) ((Bin x1 t1 t2 (s1 + 1)) `withProof` lemma_isLowerBound_transitive x2 x1 t1))

{-@ data PList a < p :: a -> a -> Bool> =
        Nil
      | Cons { phd :: a, ptl :: PList < p >  a < p phd > }  @-}
data PList a = Nil | Cons a (PList a)

{-@ measure len @-}
{-@ len :: PList a -> Nat @-}
len :: PList a -> Int
len Nil = 0
len (Cons _ t) = 1 + len t

{-@ data BinomialBit a =
        Zero { zorder :: Nat }
      | One  {  oorder :: Nat, pennant :: {p : Pennant a | psize p == oorder}}  @-}
data BinomialBit a = Zero Int | One Int (Pennant a)
  deriving (Show, Eq)

binTree :: BinomialBit Int
binTree = One 2 (P 3 2 (Bin 4 (Bin 7 Empty Empty 1) (Bin 3 Empty Empty 1) 2))

{-@ measure rank @-}
{-@ rank :: BinomialBit a -> Nat @-}
rank :: BinomialBit a -> Int
rank (Zero r) = r
rank (One r _) = r

{-@ type BinomialHeap a = PList <{\hd v -> (rank hd) == (rank v) + 1 }> (BinomialBit a) @-}
type BinomialHeap a = PList (BinomialBit a)

{-@ reflect isNil @-}
{-@ isNil :: BinomialHeap a ->  Bool @-}
isNil :: BinomialHeap a -> Bool
isNil Nil = True
isNil _ = False

{-@ reflect bRank @-}
{-@  bRank :: BinomialHeap a -> Nat @-}
bRank :: BinomialHeap a -> Int
bRank Nil = 0
bRank (Cons b bs) = rank b

{-@ bheap:: BinomialHeap Int @-}
bheap :: BinomialHeap Int
bheap = Cons (Zero 1) (Cons (One 0 (singleton 1)) Nil)

{-@ bSum:: b1: BinomialBit a -> b2: { b: BinomialBit a | rank b == rank b1} -> {b: BinomialBit a | rank b == rank b1}  @-}
bSum :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a
bSum (Zero r1) (Zero r2) = Zero r1
bSum (Zero r1) (One _ p2) = One r1 p2
bSum (One _ p1) (Zero r2) = One r2 p1
bSum (One r1 _) (One _ _) = Zero r1

{-@ bHalfAdder :: b1: BinomialBit a
               -> b2: {b: BinomialBit a | rank b == rank b1}
               -> (BinomialBit a, BinomialBit a)<{\s c -> rank s == rank b1 && rank c == rank b1 + 1}> @-}
bHalfAdder :: (Ord a) => BinomialBit a -> BinomialBit a -> (BinomialBit a, BinomialBit a)
bHalfAdder b1 b2 = (bSum b1 b2, bCarry b1 b2)

{-@ bFullAdder :: b1: BinomialBit a
               -> b2: {b: BinomialBit a | rank b == rank b1}
               -> c: {b: BinomialBit a | rank b == rank b1}
               -> (BinomialBit a, BinomialBit a)<{\s co -> rank s == rank b1 && rank co == rank b1 + 1}> @-}
bFullAdder :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a -> (BinomialBit a, BinomialBit a)
bFullAdder b1 b2 c =
  let (s, c1) = bHalfAdder b1 b2
      (s', c2) = bHalfAdder s c
   in (s', bSum c1 c2)

{-@ bCarry:: Ord a => b1: {b: BinomialBit a | rank b >= 0} -> b2: {b: BinomialBit a | rank b == rank b1} -> {b: BinomialBit a | rank b == rank b1 + 1}  @-}
bCarry :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a
bCarry (Zero r1) (Zero r2) = Zero (r1 + 1)
bCarry (Zero r1) (One _ p2) = Zero (r1 + 1)
bCarry (One _ p1) (Zero r2) = Zero (r2 + 1)
bCarry (One r1 p1) (One _ p2) = One (r1 + 1) (merge p1 p2)

{-@ bAdd :: {h1: BinomialHeap a | bRank h1 == 0} -> {h2: BinomialHeap a | bRank h2 == 0} -> BinomialHeap a @-}
bAdd :: (Ord a) => BinomialHeap a -> BinomialHeap a -> BinomialHeap a
bAdd xs ys = addWithCarry xs ys (Zero 0)

-- Helper lemma: if we have Cons x xs, then rank x == bRank (Cons x xs)
{-@ lemma_cons_rank :: x:BinomialBit a -> xs:BinomialHeap a -> {rank x == bRank (Cons x xs)} @-}
lemma_cons_rank :: BinomialBit a -> BinomialHeap a -> Proof
lemma_cons_rank x xs = ()

-- Helper lemma: if bRank h1 == bRank h2 and both are Cons, their heads have equal rank
{-@ lemma_equal_brank :: h1:{BinomialHeap a | not (isNil h1)}
                      -> h2:{BinomialHeap a | not (isNil h2) && bRank h2 == bRank h1}
                      -> {bRank h1 == bRank h2} @-}
lemma_equal_brank :: BinomialHeap a -> BinomialHeap a -> Proof
lemma_equal_brank _ _ = ()

{-@ addWithCarry :: h1: BinomialHeap a
                  -> {h2: BinomialHeap a |  (bRank h2 == bRank h1 || isNil h1) || isNil h2 }
                  -> carry: { c : BinomialBit a | ((not isNil h1) => rank carry == bRank h1) && ((not isNil h2) => rank carry == bRank h2)}
                  -> {b: BinomialHeap a | ((not isNil h1) => rank carry == bRank h1) && ((not isNil h2) => rank carry == bRank h2)} / [len h1, len h2]@-}
addWithCarry :: (Ord a) => BinomialHeap a -> BinomialHeap a -> BinomialBit a -> BinomialHeap a
addWithCarry Nil Nil c
  | c == (Zero 0) = Nil
  | otherwise = Cons c Nil
addWithCarry (Cons x xs) Nil (Zero r) = Cons x xs
addWithCarry (Cons x xs) Nil c@(One r _) =
  let (s, c') = bFullAdder x (Zero (rank x)) c
   in Cons s (addWithCarry xs Nil c')
addWithCarry Nil (Cons y ys) c =
  let z = Zero (rank y)
      (s, c') = bFullAdder z y c
   in Cons s (addWithCarry Nil ys c')
addWithCarry (Cons x xs) (Cons y ys) c =
  let (s, c') = bFullAdder x y c
   in Cons s (addWithCarry xs ys c')
