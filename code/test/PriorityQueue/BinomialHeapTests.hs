{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PriorityQueue.BinomialHeapTests where

import PriorityQueue.BinomialHeap
import Test.Tasty
import Test.Tasty.HUnit

binomialHeapTests :: TestTree
binomialHeapTests =
  testGroup
    "PriorityQueue.BinomialHeap"
    [ testCase "singleton" $
        let p = singleton 5 :: Pennant Int
         in assertEqual "pheight of singleton should be 0" 0 (pheight p)
    , testCase "link two pennants" $
        let p1 = singleton 5 :: Pennant Int
            p2 = singleton 10 :: Pennant Int
            linked = link p1 p2
         in do
              assertEqual "pheight of linked should be 1" 1 (pheight linked)
              assertEqual "root of linked should be smaller" 5 (root linked)
    , testCase "link two pennants, second smaller" $
        let p1 = singleton 10 :: Pennant Int
            p2 = singleton 5 :: Pennant Int
            linked = link p1 p2
         in do
              assertEqual "pheight of linked should be 1" 1 (pheight linked)
              assertEqual "root of linked should be smaller" 5 (root linked)
    , testCase "extractMin from a simple heap" $
        let
          -- A heap with a single element {1}
          h = Cons (One 0 (singleton 1)) Nil :: BinomialHeap Int
          expected = (singleton 1, Nil)
         in
          assertEqual "extractMin should get the only element" expected (extractMin h)
    , testCase "extractMin from a heap with two elements" $
        let p1 = singleton (1 :: Int)
            p2 = singleton (2 :: Int)
            h = bAdd (Cons (One 0 p1) Nil) (Cons (One 0 p2) Nil)
            -- h is Cons (Zero 0) (Cons (One 1 (link p1 p2)) Nil)
            (minPennant, restHeap) = extractMin h
         in do
              assertEqual "min value" 1 (root minPennant)
              -- The rest of the heap is what remains after removing the pennant with the min root.
              -- In this implementation, it seems the children of the extracted pennant are not re-inserted into the heap.
              -- So the remaining heap will not contain '2'.
              -- The returned pennant itself contains '2'.
              assertEqual "pennant contains 2" (Bin 2 Empty Empty 0) (bin minPennant)
              assertEqual "remaining heap" (Cons (Zero 0) Nil) restHeap
    , testCase "extractMin from a more complex heap" $
        -- h1 represents {1}
        let h1 = Cons (One 0 (singleton (1 :: Int))) Nil :: BinomialHeap Int
            -- h2 represents {2}
            h2 = Cons (One 0 (singleton (2 :: Int))) Nil :: BinomialHeap Int
            -- h3 represents {3}
            h3 = Cons (One 0 (singleton (3 :: Int))) Nil :: BinomialHeap Int
            -- h12 is {1,2}
            h12 = bAdd h1 h2
            -- h is {1,2,3}
            h = bAdd h12 h3
            -- h12 = Cons (Zero 0) (Cons (One 1 (link (singleton 1) (singleton 2))) Nil)
            -- h = bAdd h12 h3
            -- addWithCarry (Cons (Zero 0) (Cons (One 1 (link (singleton 1) (singleton 2))) Nil)) (Cons (One 0 (singleton 3)) Nil) (Zero 0)
            -- s,c' = bFullAdder (Zero 0) (One 0 (singleton 3)) (Zero 0) -> (One 0 (singleton 3)), (Zero 1)
            -- Cons (One 0 (singleton 3)) (addWithCarry (Cons (One 1 (link (singleton 1) (singleton 2))) Nil) Nil (Zero 1))
            -- addWithCarry (Cons (One 1 ..) Nil) Nil (Zero 1)
            -- s,c' = bFullAdder (One 1 ..) (Zero 1) (Zero 1) -> (One 1 ..), (Zero 2)
            -- Cons (One 1 ..) (addWithCarry Nil Nil (Zero 2))
            -- addWithCarry Nil Nil (Zero 2) -> Cons (Zero 2) Nil
            -- h = Cons (One 0 (singleton 3)) (Cons (One 1 (link (singleton 1) (singleton 2))) (Cons (Zero 2) Nil))
            (minPennant, restHeap) = extractMin h
         in do
              assertEqual "min value" 1 (root minPennant)
              assertEqual "h" (Cons (One 0 (singleton 3)) (Cons (One 1 (link (singleton 1) (singleton 2))) Nil)) h
              assertEqual "remaining heap" (Cons (One 0 (singleton 3)) Nil) restHeap
    ]
