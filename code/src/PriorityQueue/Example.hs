module PriorityQueue.Example where

import PriorityQueue.LeftistHeap
import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ heap1:: Heap Int @-}
heap1 :: Heap Int
heap1 = Node 1 (Node 2 Empty Empty 1) (Node 3 Empty Empty 1) 2

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

data Sparse a = SP
  { spDim :: Int
  , spElems :: [(Int, a)]
  }

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
