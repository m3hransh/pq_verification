{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PriorityQueue.BinomialHeapTests where

import PriorityQueue.Base
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
    , testCase "dismantle empty tree" $
        let rev = dismantle Empty :: ReversedBinomialHeap Int
         in assertEqual "dismantle Empty should be RNil" RNil rev
    , testCase "dismantle singleton tree" $
        let tree = Bin 5 Empty Empty 0
            rev = dismantle tree
         in do
              assertEqual "should produce single One bit" (RCons (One 0 (singleton 5)) RNil) rev
              assertEqual "ranks should decrease" True (isRNil (rtl rev))
    , testCase "dismantle binomial tree of height 2" $
        let
          -- Binomial tree B2 with min element 1
          tree = Bin 1 (Bin 3 Empty Empty 0) (Bin 2 Empty Empty 0) 1
          rev = dismantle tree
         in
          -- Should produce: One(1, P(1, 1, Bin 3..)) -> One(0, P(2, 0, Empty))
          do
            -- First element should have rank 1
            assertBool "should not be empty" (not (isRNil rev))
            assertEqual "first rank should be 1" 1 (rank (rbhead rev))
            -- Second element should have rank 0 (decreasing by 1)
            let rest = rtl rev
            assertBool "rest should not be empty" (not (isRNil rest))
            assertEqual "second rank should be 0" 0 (rank (rbhead rest))
    , testCase "reverseToBinomialHeap empty" $
        let rev = RNil :: ReversedBinomialHeap Int
            heap = reverseToBinomialHeap rev
         in assertEqual "reverse empty should be empty" Nil heap
    , testCase "reverseToBinomialHeap single element" $
        let rev = RCons (One 0 (singleton 5)) RNil
            heap = reverseToBinomialHeap rev
         in assertEqual "reverse single element" (Cons (One 0 (singleton 5)) Nil) heap
    , testCase "reverseToBinomialHeap two elements with decreasing ranks" $
        let p0 = singleton (10 :: Int)
            p1 = link (singleton 5) (singleton 7)
            rev = RCons (One 1 p1) (RCons (One 0 p0) RNil)
            heap = reverseToBinomialHeap rev
         in do
              assertEqual "heap should not be empty" False (heapIsEmpty heap)
              assertEqual "first bit should have rank 0" 0 (rank (bhead heap))
              case heap of
                Cons _ (Cons _ _) -> assertEqual "second bit should have rank 1" 1 (rank (bhead (tl heap)))
                _ -> assertFailure "heap should have at least 2 elements"
    , testCase "reverseToBinomialHeap preserves structure" $
        let
          -- Create a binomial tree and dismantle it
          tree = Bin 1 (Bin 3 Empty Empty 0) (Bin 2 Empty Empty 0) 1
          rev = dismantle tree
          -- Reverse back to binomial heap
          heap = reverseToBinomialHeap rev
         in
          do
            assertBool "heap should not be empty" (not (heapIsEmpty heap))
            assertEqual "first rank should be 0" 0 (rank (bhead heap))
            case heap of
              Cons _ rest -> do
                assertBool "rest should not be empty" (not (heapIsEmpty rest))
                assertEqual "second rank should be 1" 1 (rank (bhead rest))
              _ -> assertFailure "heap should not be empty"
    , testCase "reverseToBinomialHeap three elements" $
        let p0 = singleton (20 :: Int)
            p1 = link (singleton 10) (singleton 15)
            p2 = link p1 (link (singleton 5) (singleton 8))
            rev = RCons (One 2 p2) (RCons (One 1 p1) (RCons (One 0 p0) RNil))
            heap = reverseToBinomialHeap rev
         in do
              assertBool "heap should not be empty" (not (heapIsEmpty heap))
              assertEqual "first rank should be 0" 0 (rank (bhead heap))
              case heap of
                Cons _ h1 -> do
                  assertBool "h1 should not be empty" (not (heapIsEmpty h1))
                  assertEqual "second rank should be 1" 1 (rank (bhead h1))
                  case h1 of
                    Cons _ h2 -> do
                      assertBool "h2 should not be empty" (not (heapIsEmpty h2))
                      assertEqual "third rank should be 2" 2 (rank (bhead h2))
                    _ -> assertFailure "h1 should not be empty"
                _ -> assertFailure "heap should not be empty"
    , -- PriorityQueue Operations Tests
      testCase "empty heap is empty" $
        let heap = empty :: BinomialHeap Int
         in assertEqual "empty heap should be empty" True (isEmpty heap)
    , testCase "findMin on empty heap" $
        let heap = empty :: BinomialHeap Int
         in assertEqual "findMin on empty should be Nothing" Nothing (findMin heap)
    , testCase "insert one element" $
        let heap = insert 5 (empty :: BinomialHeap Int)
         in do
              assertEqual "heap should not be empty" False (isEmpty heap)
              assertEqual "findMin should return the element" (Just 5) (findMin heap)
    , testCase "insert multiple elements" $
        let heap = insert 3 $ insert 1 $ insert 5 $ insert 2 (empty :: BinomialHeap Int)
         in do
              assertEqual "heap should not be empty" False (isEmpty heap)
              assertEqual "findMin should return minimum" (Just 1) (findMin heap)
    , testCase "splitMin on empty heap" $
        let heap = empty :: BinomialHeap Int
            result = splitMin heap
         in assertEqual "splitMin on empty should be EmptyView" EmptyView result
    , testCase "splitMin on single element heap" $
        let heap = insert 5 (empty :: BinomialHeap Int)
            result = splitMin heap
         in case result of
              EmptyView -> assertFailure "splitMin should not return EmptyView"
              Min val rest -> do
                assertEqual "min value should be 5" 5 val
                assertEqual "rest should be empty" True (isEmpty rest)
    , testCase "splitMin removes minimum" $
        let heap = insert 3 $ insert 1 $ insert 5 (empty :: BinomialHeap Int)
            result = splitMin heap
         in case result of
              EmptyView -> assertFailure "splitMin should not return EmptyView"
              Min val rest -> do
                assertEqual "min value should be 1" 1 val
                assertEqual "rest should not be empty" False (isEmpty rest)
                assertEqual "findMin of rest should be 3" (Just 3) (findMin rest)
    , testCase "multiple splitMin operations" $
        let heap = insert 5 $ insert 2 $ insert 8 $ insert 1 (empty :: BinomialHeap Int)
            Min v1 h1 = splitMin heap
            Min v2 h2 = splitMin h1
            Min v3 h3 = splitMin h2
            Min v4 h4 = splitMin h3
         in do
              assertEqual "first min" 1 v1
              assertEqual "second min" 2 v2
              assertEqual "third min" 5 v3
              assertEqual "fourth min" 8 v4
              assertEqual "final heap is empty" True (isEmpty h4)
    , testCase "merge two empty heaps" $
        let h1 = empty :: BinomialHeap Int
            h2 = empty :: BinomialHeap Int
            merged = merge h1 h2
         in assertEqual "merged heap should be empty" True (isEmpty merged)
    , testCase "merge empty with non-empty" $
        let h1 = empty :: BinomialHeap Int
            h2 = insert 5 $ insert 3 empty
            merged = merge h1 h2
         in do
              assertEqual "merged heap should not be empty" False (isEmpty merged)
              assertEqual "findMin should be 3" (Just 3) (findMin merged)
    , testCase "merge non-empty with empty" $
        let h1 = insert 7 $ insert 2 (empty :: BinomialHeap Int)
            h2 = empty
            merged = merge h1 h2
         in do
              assertEqual "merged heap should not be empty" False (isEmpty merged)
              assertEqual "findMin should be 2" (Just 2) (findMin merged)
    , testCase "merge two non-empty heaps" $
        let h1 = insert 3 $ insert 7 (empty :: BinomialHeap Int)
            h2 = insert 2 $ insert 5 empty
            merged = merge h1 h2
         in do
              assertEqual "merged heap should not be empty" False (isEmpty merged)
              assertEqual "findMin should be 2" (Just 2) (findMin merged)
    , testCase "merge preserves all elements" $
        let h1 = insert 4 $ insert 2 (empty :: BinomialHeap Int)
            h2 = insert 5 $ insert 1 empty
            merged = merge h1 h2
            Min v1 m1 = splitMin merged
            Min v2 m2 = splitMin m1
            Min v3 m3 = splitMin m2
            Min v4 m4 = splitMin m3
         in do
              assertEqual "first" 1 v1
              assertEqual "second" 2 v2
              assertEqual "third" 4 v3
              assertEqual "fourth" 5 v4
              assertEqual "final empty" True (isEmpty m4)
    , testCase "complex sequence of operations" $
        let h0 = empty :: BinomialHeap Int
            h1 = insert 10 h0
            h2 = insert 5 h1
            h3 = insert 15 h2
            Min _ h4 = splitMin h3
            h5 = insert 3 h4
            h6 = insert 20 h5
            merged = merge h6 (insert 1 $ insert 7 empty)
         in do
              assertEqual "findMin after operations" (Just 1) (findMin merged)
              let Min _ rest = splitMin merged
              assertEqual "second min" (Just 3) (findMin rest)
    , testCase "insert and extract in sorted order" $
        let heap = foldr insert (empty :: BinomialHeap Int) [9, 2, 7, 1, 8, 5, 3, 6, 4]
            extract EmptyView acc = reverse acc
            extract (Min v rest) acc = extract (splitMin rest) (v : acc)
            sorted = extract (splitMin heap) []
         in assertEqual "should extract in sorted order" [1, 2, 3, 4, 5, 6, 7, 8, 9] sorted
    , testCase "stress test - many elements" $
        let heap = foldr insert (empty :: BinomialHeap Int) [100, 99 .. 1]
         in do
              assertEqual "findMin of large heap" (Just 1) (findMin heap)
              let Min _ rest = splitMin heap
              assertEqual "second min of large heap" (Just 2) (findMin rest)
    , testCase "bAdd: two empty heaps" $
        let h1 = Nil :: BinomialHeap Int
            h2 = Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in assertEqual "bAdd empty heaps should be empty" Nil result
    , testCase "bAdd: single element heaps" $
        let h1 = Cons (One 0 (singleton 5)) Nil :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 3)) Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              assertEqual "should not be all zeros" False (hasOnlyZeros result)
              assertEqual "min should be 3" 3 (minRootInHeap result)
    , testCase "bAdd: with empty heap" $
        let h1 = Cons (One 0 (singleton 5)) Nil :: BinomialHeap Int
            h2 = Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              assertEqual "result should equal h1" h1 result
              assertEqual "min should be 5" 5 (minRootInHeap result)
    , testCase "bAdd: empty with non-empty" $
        let h1 = Nil :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 7)) Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              assertEqual "should not be all zeros" False (hasOnlyZeros result)
              assertEqual "min should be 7" 7 (minRootInHeap result)
              -- Verify element is present
              let Min v h' = splitMin result
              assertEqual "extracted value is 7" 7 v
              assertEqual "heap is empty after extraction" True (isEmpty h')
    , testCase "bAdd: heap with Zero bit and single element" $
        let h1 = Cons (Zero 0) (Cons (One 1 (link (singleton 1) (singleton 2))) Nil) :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 3)) Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              assertEqual "should not be all zeros" False (hasOnlyZeros result)
              assertEqual "min should be 1" 1 (minRootInHeap result)
              -- Verify all three elements are present
              let Min v1 h' = splitMin result
              assertEqual "first min is 1" 1 v1
              let Min v2 h'' = splitMin h'
              assertEqual "second min is 2" 2 v2
              let Min v3 h''' = splitMin h''
              assertEqual "third min is 3" 3 v3
    , testCase "bAdd: carry propagation bug" $
        let h1 = Cons (One 0 (singleton 1)) (Cons (One 1 (link (singleton 3) (singleton 4))) Nil) :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 2)) Nil :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              -- BUG: This currently fails! The result has only zeros
              assertEqual "should not be all zeros (BUG!)" False (hasOnlyZeros result)
              -- Should contain all 4 elements: 1, 2, 3, 4
              let Min v1 h' = splitMin result
              assertEqual "first min is 1" 1 v1
              let Min v2 h'' = splitMin h'
              assertEqual "second min is 2" 2 v2
              let Min v3 h''' = splitMin h''
              assertEqual "third min is 3" 3 v3
              let Min v4 h4 = splitMin h'''
              assertEqual "fourth min is 4" 4 v4
              assertEqual "heap should be empty after 4 extractions" True (isEmpty h4)
    , testCase "bAdd: three elements" $
        let h1 = Cons (One 0 (singleton 1)) Nil :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 2)) Nil :: BinomialHeap Int
            h12 = bAdd h1 h2
            h3 = Cons (One 0 (singleton 3)) Nil :: BinomialHeap Int
            result = bAdd h12 h3
         in do
              assertEqual "should not be all zeros" False (hasOnlyZeros result)
              assertEqual "min should be 1" 1 (minRootInHeap result)
              -- Verify all three elements
              let Min v1 h' = splitMin result
              assertEqual "first min is 1" 1 v1
              let Min v2 h'' = splitMin h'
              assertEqual "second min is 2" 2 v2
              let Min v3 h''' = splitMin h''
              assertEqual "third min is 3" 3 v3
    , testCase "bAdd: multiple carries" $
        let h1 = Cons (One 0 (singleton 1)) (Cons (One 1 (link (singleton 2) (singleton 3))) (Cons (One 2 (link (link (singleton 4) (singleton 5)) (link (singleton 6) (singleton 7)))) Nil)) :: BinomialHeap Int
            h2 = Cons (One 0 (singleton 8)) (Cons (One 1 (link (singleton 9) (singleton 10))) (Cons (One 2 (link (link (singleton 11) (singleton 12)) (link (singleton 13) (singleton 14)))) Nil)) :: BinomialHeap Int
            result = bAdd h1 h2
         in do
              assertEqual "should not be all zeros" False (hasOnlyZeros result)
              assertEqual "min should be 1" 1 (minRootInHeap result)
    ]
