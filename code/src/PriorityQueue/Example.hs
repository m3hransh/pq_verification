module PriorityQueue.Example where

import PriorityQueue.LeftistHeap
import Prelude hiding (min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}

{-@ heap1:: Heap Int @-}
heap1 :: Heap Int
heap1 = Node 1 (Node 2 Empty Empty 1) (Node 3 Empty Empty 1) 2
