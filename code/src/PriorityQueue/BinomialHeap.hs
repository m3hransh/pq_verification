module PriorityQueue.BinomialHeap where

import Control.Arrow (Arrow (second))
import qualified Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (max, min, sum)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect max @-}
{-@ max:: forall <p :: Int -> Bool> . Int <p> -> Int<p> -> Int<p> @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ reflect min @-}
{-@ min:: (Ord a) => a -> a -> a @-}
min :: (Ord a) => a -> a -> a
min x y = if x <= y then x else y

-- Binary tree with heap property
{-@ reflect isLowerBound @-}
{-@ isLowerBound :: Ord a => v:a -> t:BinTree a -> Bool @-}
isLowerBound :: (Ord a) => a -> BinTree a -> Bool
isLowerBound _ Empty = True
isLowerBound v (Bin x l r _) = v <= x && isLowerBound v l && isLowerBound v r

{-@ lemma_isLowerBound_transitive :: x:a -> y:{a | x <= y} -> t:{BinTree a | isLowerBound y t} -> {isLowerBound x t} @-}
lemma_isLowerBound_transitive ::
  (Ord a) => a -> a -> BinTree a -> Proof
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

{-@ measure treeHeight @-}
treeHeight :: BinTree a -> Int
treeHeight Empty = 0
treeHeight (Bin _ l r _) = 1 + max (treeHeight l) (treeHeight r)

{-@ invariant {t:BinTree a | height t = treeHeight t} @-}

{-@ measure bheight @-}
{-@ bheight :: BinTree a -> {v: Int | v >= -1} @-}
bheight :: BinTree a -> Int
bheight Empty = -1
bheight (Bin _ _ _ h) = h

{-@ data Pennant a = P { root :: a
           ,pheight  :: Nat
           ,bin   :: {b : BinTreeBound a root | bheight b + 1 = pheight}
           }
  @-}
data Pennant a
  = P
  { root :: a
  , pheight :: Int
  , bin :: (BinTree a)
  }
  deriving (Show, Eq)

pennantExample :: Pennant Int
pennantExample = P 3 2 (Bin 4 (Bin 7 Empty Empty 0) (Bin 3 Empty Empty 0) 1)

{-@ singleton :: Ord a => a -> {v:Pennant a | pheight v == 0} @-}
singleton :: (Ord a) => a -> Pennant a
singleton x = P x 0 Empty

{-@ measure isEmpty @-}
{-@ isEmpty :: Pennant a -> Bool @-}
isEmpty :: Pennant a -> Bool
isEmpty _ = False

{-@reflect bag @-}
{-@ bag :: BinTree a -> Bag a @-}
bag :: (Ord a) => BinTree a -> B.Bag a
bag Empty = B.empty
bag (Bin a l r _) = B.put a (B.union (bag l) (bag r))

{-@reflect pBag @-}
{-@ pBag :: Pennant a -> Bag a @-}
pBag :: (Ord a) => Pennant a -> B.Bag a
pBag (P a _ bt) = B.put a (bag bt)

{-@ predicate BagUnion H1 H2 H = (pBag H == B.union (pBag H1) (pBag H2)) @-}

{-@reflect link @-}
{-@ link :: Ord a => t1: Pennant a -> t2: {t : Pennant a | pheight t == pheight t1} -> {v: Pennant a| pheight v == pheight t1 + 1 && BagUnion t1 t2 v} @-}
link :: (Ord a) => Pennant a -> Pennant a -> Pennant a
link (P x1 s1 t1) (P x2 s2 t2)
  | x1 <= x2 = (P x1 (s1 + 1) ((Bin x2 t2 t1 (s1)) `withProof` (lemma_isLowerBound_transitive x1 x2 t2)))
  | otherwise = (P x2 (s1 + 1) ((Bin x1 t1 t2 (s1)) `withProof` lemma_isLowerBound_transitive x2 x1 t1))

{-@ data BinomialBit a =
        Zero { zorder :: Nat }
      | One  {  oorder :: Nat, pennant :: {p : Pennant a | pheight p == oorder}}  @-}
data BinomialBit a
  = Zero Int
  | One Int (Pennant a)
  deriving (Show, Eq)

binTree :: BinomialBit Int
binTree = One 2 (P 3 2 (Bin 4 (Bin 7 Empty Empty 0) (Bin 3 Empty Empty 0) 1))

{-@ measure rank @-}
{-@ rank :: BinomialBit a -> Nat @-}
rank :: BinomialBit a -> Int
rank (Zero r) = r
rank (One r _) = r

-- Refined data definition for BinomialHeap that checks only immediate neighbors
{-@ data BinomialHeap [len] a =
        Nil
      | Cons { phd :: BinomialBit a
             , ptl :: {bs : BinomialHeap a | not (isNil bs) => rank ( bhead bs) = (rank phd) + 1}
             }
@-}
-- Plain PList without parameterized invariant
data BinomialHeap a
  = Nil
  | Cons
      { phd :: BinomialBit a
      , ptl :: (BinomialHeap a)
      }
  deriving (Show, Eq)

{-@ measure len @-}
{-@ len :: BinomialHeap a -> Nat @-}
len :: BinomialHeap a -> Int
len Nil = 0
len (Cons _ t) = 1 + len t

{-@ measure isNil @-}
{-@ isNil ::BinomialHeap a ->  Bool @-}
isNil :: BinomialHeap a -> Bool
isNil Nil = True
isNil _ = False

{-@ measure bhead @-}
{-@ bhead :: {b: BinomialHeap a| not (isNil b)} -> BinomialBit a @-}
bhead :: BinomialHeap a -> BinomialBit a
bhead (Cons a _) = a

-- Example 1: Single Zero bit at rank 0
{-@ ex1 :: BinomialHeap Int @-}
ex1 :: BinomialHeap Int
ex1 = Cons (Zero 0) Nil

-- Example 2: Two bits with consecutive ranks 0, 1
{-@ ex2 :: BinomialHeap Int @-}
ex2 :: BinomialHeap Int
ex2 = Cons (Zero 0) (Cons (Zero 1) Nil)

-- Example 3: Three bits with consecutive ranks 0, 1, 2
{-@ ex3 :: BinomialHeap Int @-}
ex3 :: BinomialHeap Int
ex3 = Cons (Zero 0) (Cons (Zero 1) (Cons (Zero 2) Nil))

-- Example 4: Mix of Zero and One bits with consecutive ranks
{-@ ex4 :: BinomialHeap Int @-}
ex4 :: BinomialHeap Int
ex4 = Cons (One 0 (singleton 1)) (Cons (Zero 1) Nil)

-- Example 5: The original example
{-@ ex5 :: BinomialHeap Int @-}
ex5 :: BinomialHeap Int
ex5 = Cons (Zero 1) Nil

{-@ measure bRank @-}
{-@ bRank :: BinomialHeap a -> Nat @-}
bRank :: BinomialHeap a -> Int
bRank Nil = 0
bRank (Cons b bs) = rank b

{-@ bheap:: BinomialHeap Int @-}
bheap :: BinomialHeap Int
bheap = Cons (One 0 (singleton 1)) (Cons (Zero 1) Nil)

{-@ reflect bSum @-}
{-@ bSum:: b1: BinomialBit a -> b2: { b: BinomialBit a | rank b == rank b1} -> {b: BinomialBit a | rank b == rank b1}  @-}
bSum :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a
bSum (Zero r1) (Zero r2) = Zero r1
bSum (Zero r1) (One _ p2) = One r1 p2
bSum (One _ p1) (Zero r2) = One r2 p1
bSum (One r1 _) (One _ _) = Zero r1

{-@ reflect zero @-}
{-@ zero :: BinomialBit a @-}
zero :: BinomialBit a
zero = Zero 0

{-@ reflect bHalfAdder @-}
{-@ bHalfAdder :: b1: BinomialBit a
               -> b2: {b: BinomialBit a | rank b == rank b1}
               -> (BinomialBit a, BinomialBit a)<{\s c -> rank s == rank b1 && rank c == rank b1 + 1}> @-}
bHalfAdder :: (Ord a) => BinomialBit a -> BinomialBit a -> (BinomialBit a, BinomialBit a)
bHalfAdder b1 b2 = (bSum b1 b2, bCarry b1 b2)

{-@ reflect bFullAdder @-}
{-@ bFullAdder :: b1: BinomialBit a
               -> b2: {b: BinomialBit a | rank b == rank b1}
               -> c: {b: BinomialBit a | rank b == rank b1}
               -> ({s: BinomialBit a | rank s == rank b1} , {co: BinomialBit a | rank co == rank b1 + 1}) @-}
bFullAdder :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a -> (BinomialBit a, BinomialBit a)
bFullAdder b1 b2 c =
  let (s, c1) = bHalfAdder b1 b2
      (s', c2) = bHalfAdder s c
   in (s', bSum c1 c2)

{-@ reflect bCarry @-}
{-@ bCarry:: Ord a => b1: {b: BinomialBit a | rank b >= 0} -> b2: {b: BinomialBit a | rank b == rank b1} -> {b: BinomialBit a | rank b == rank b1 + 1}  @-}
bCarry :: (Ord a) => BinomialBit a -> BinomialBit a -> BinomialBit a
bCarry (Zero r1) (Zero r2) = Zero (r1 + 1)
bCarry (Zero r1) (One _ p2) = Zero (r1 + 1)
bCarry (One _ p1) (Zero r2) = Zero (r2 + 1)
bCarry (One r1 p1) (One _ p2) = One (r1 + 1) (link p1 p2)

{-@ reflect bAdd @-}
{-@ bAdd :: {h1: BinomialHeap a | bRank h1 == 0} -> {h2: BinomialHeap a | bRank h2 == 0} -> BinomialHeap a @-}
bAdd :: (Ord a) => BinomialHeap a -> BinomialHeap a -> BinomialHeap a
bAdd xs ys = addWithCarry xs ys (Zero 0)

{-@ reflect addWithCarry @-}
{-@ addWithCarry :: h1: BinomialHeap a
                       -> {h2: BinomialHeap a | (bRank h2 == bRank h1 || isNil h1) || isNil h2 }
                       -> carry: { c : BinomialBit a | ((not isNil h1) => rank carry == bRank h1) && ((not isNil h2) => rank carry == bRank h2)}
                       -> {b: BinomialHeap a | (not isNil b) => rank (bhead b) == rank carry} / [len h1, len h2]
     @-}
addWithCarry :: (Ord a) => BinomialHeap a -> BinomialHeap a -> BinomialBit a -> BinomialHeap a
addWithCarry Nil Nil c
  | c == (Zero 0) = Nil
  | otherwise = Cons c Nil
addWithCarry (Cons x xs) Nil (Zero r) = Cons x xs
addWithCarry (Cons x xs) Nil c@(One r _) =
  let z = Zero (rank x)
      (s, c') = bFullAdder x z c
   in case xs of
        Nil -> Cons s Nil
        Cons x' xs' -> (Cons s (addWithCarry xs Nil c'))
addWithCarry Nil (Cons y ys) c =
  let z = Zero (rank y)
      (s, c') = bFullAdder z y c
   in case ys of
        Nil -> Cons s Nil
        Cons y' ys' -> Cons s (addWithCarry Nil ys c')
addWithCarry (Cons x xs) (Cons y ys) c =
  let (s, c') = bFullAdder x y c
   in case (xs, ys) of
        (Nil, Nil) -> Cons s (addWithCarry Nil Nil c')
        (Cons x' xs', Nil) -> Cons s (addWithCarry xs Nil c')
        (Nil, Cons y' ys') -> Cons s (addWithCarry Nil ys c')
        (Cons x' xs', Cons y' ys') -> Cons s (addWithCarry xs ys c')

-- Helper function to check if a heap contains only Zero bits
{-@ reflect hasOnlyZeros @-}
{-@ hasOnlyZeros :: BinomialHeap a -> Bool @-}
hasOnlyZeros :: BinomialHeap a -> Bool
hasOnlyZeros Nil = True
hasOnlyZeros (Cons z@(Zero _) bs) = hasOnlyZeros bs
hasOnlyZeros (Cons (One _ _) _) = False

-- Helper function to get the minimum root value from a heap (reflected function, not a measure)
{-@ reflect minRootInHeap @-}
{-@ minRootInHeap :: Ord a => {h:BinomialHeap a | not (hasOnlyZeros h)} -> a @-}
minRootInHeap :: (Ord a) => BinomialHeap a -> a
minRootInHeap (Cons (Zero _) bs) = minRootInHeap bs
minRootInHeap (Cons (One _ (P r _ _)) Nil) = r
minRootInHeap (Cons (One _ (P r _ _)) bs@(Cons _ _)) =
  if hasOnlyZeros bs
    then r
    else min r (minRootInHeap bs)

{-@ extractMin :: (Ord a) => {h:BinomialHeap a | not (hasOnlyZeros h)}
                  -> ({p:Pennant a | minRootInHeap h == (root p)}, {h':BinomialHeap a | not (isNil h') => rank (bhead h') == rank (bhead h) }) @-}
extractMin :: (Ord a) => BinomialHeap a -> (Pennant a, BinomialHeap a)
extractMin (Cons b Nil) =
  case b of
    One _ p -> (p, Nil)
    _ -> error "Unreachable: hasOnlyZeros implies no One bits"
extractMin (Cons z@(Zero r) bs@(Cons b tbs)) =
  if hasOnlyZeros bs
    then case b of
      One _ p -> (p, Nil)
      _ -> error "Unreachable: hasOnlyZeros implies no One bits"
    else case extractMin bs of
      (b, bs') -> (b, Cons z bs')
extractMin (Cons o@(One r p@(P m _ _)) bs@(Cons b tbs)) =
  if hasOnlyZeros bs
    then (p, Nil)
    else case extractMin bs of
      (p'@(P m' _ _), bs')
        | m <= m' -> (p, Cons (Zero r) bs)
        | otherwise -> case bs' of
            Nil -> (p', Cons o Nil)
            Cons _ _ -> (p', Cons o bs')

-- ismantle :: (Ord a) => BinTree a -> PList (BinomialBit a)
-- dismantle Empty = Nil
-- dismantle (Bin m l r h) = Cons (One h (P m (h - 1) l)) (dismantle r)
