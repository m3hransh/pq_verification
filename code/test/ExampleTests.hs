{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ExampleTests where

import Control.Exception (SomeException, try)
import Example
-- import Language.Haskell.Liquid.ProofCombinators
import Test.Tasty
import Test.Tasty.HUnit

exampleTests :: TestTree
exampleTests =
  testGroup
    "Example"
    [ testCase "Find the minimum element in List Heap" $
        let pq = insert 2 (insert 1 (insert 4 empty)) :: PList Int
         in assertEqual "Should return the element at the given index" (findMin pq) (Just 1)
    , testCase "Find the minimum element in empty List Heap" $
        let pq = empty :: PList Int
         in assertEqual "Should return the element at the given index" (findMin pq) (Nothing)
    , testCase "Find the minimum element in ToppedTree Heap" $
        let pq = insert 2 (insert 1 (insert 4 empty)) :: ToppedTree Int
         in assertEqual "Should return the element at the given index" (findMin pq) (Just 1)
    , testCase "Find the minimum element in empty ToppedTree Heap" $
        let pq = empty :: ToppedTree Int
         in assertEqual
              "Should return the element at the given index"
              (findMin pq)
              (Nothing)
    , testCase "Addition for Binary Digits" $
        let result = add ([1, 0, 1] :: [Int]) ([1, 1] :: [Int])
         in assertEqual "0 + 0 should be 0" ([0, 0, 0, 1] :: [Int]) result
    , testCase "Addition with carry" $
        let result = add ([1, 1, 1] :: [Int]) ([1, 1, 1] :: [Int])
         in assertEqual "1 + 1 + carry" ([0, 1, 1, 1] :: [Int]) result
    , testCase "Addition with different lengths" $
        let result = add ([1, 0] :: [Int]) ([1, 1, 1] :: [Int])
         in assertEqual "Different lengths" ([0, 0, 0, 1] :: [Int]) result
    , testCase "Addition with empty list" $
        let result = add ([] :: [Int]) ([1, 0, 1] :: [Int])
         in assertEqual "Empty left operand" ([1, 0, 1] :: [Int]) result
    , testCase "Addition with both empty lists" $
        let result = add ([] :: [Int]) ([] :: [Int])
         in assertEqual "Both operands empty" ([] :: [Int]) result
    , testCase "Addition with leading zeros" $
        let result = add ([0, 0, 1] :: [Int]) ([0, 1] :: [Int])
         in assertEqual "Leading zeros" ([0, 1, 1] :: [Int]) result
    , testCase "Addition with leading zeros" $
        let result = add ([0, 0, 1] :: [Int]) ([0, 1] :: [Int])
         in assertEqual "Leading zeros" ([0, 1, 1] :: [Int]) result
    , testCase "ToppedTree Addition for Binary Digits" $
        let b1 = [EmptyView, EmptyView, Min 3 (BNode 5 (BNode 2 BLeaf BLeaf) (BNode 4 BLeaf BLeaf))] :: [ToppedTree Int]
            b2 = [EmptyView, EmptyView, Min 1 (BNode 3 (BNode 14 BLeaf BLeaf) (BNode 2 BLeaf BLeaf))] :: [ToppedTree Int]
            result = add b1 b2
            expected = [EmptyView, EmptyView, EmptyView, Min 1 (BNode 3 (BNode 5 (BNode 2 BLeaf BLeaf) (BNode 4 BLeaf BLeaf)) (BNode 3 (BNode 14 BLeaf BLeaf) (BNode 2 BLeaf BLeaf)))] :: [ToppedTree Int]
         in assertEqual "ToppedTree binary addition" expected result
      , testCase "Find the minimum element in BinomialHeap" $
          let pq = insert 2 (insert 1 (insert 4 empty)) :: BinomialHeap Int
           in assertEqual "Should return the minimum element" (findMin pq) (Just 1)
      , testCase "Find the minimum element in empty BinomialHeap" $
          let pq = empty :: BinomialHeap Int
           in assertEqual "Should return Nothing for empty heap" (findMin pq) Nothing
      , testCase "Check if BinomialHeap is empty" $
          let emptyPq = empty :: BinomialHeap Int
              nonEmptyPq = insert 5 empty :: BinomialHeap Int
           in do
                assertEqual "Empty heap should be empty" True (isEmpty emptyPq)
                assertEqual "Non-empty heap should not be empty" False (isEmpty nonEmptyPq)
      , testCase "Insert and find minimum in BinomialHeap" $
          let pq1 = insert 10 empty :: BinomialHeap Int
              pq2 = insert 5 pq1
              pq3 = insert 15 pq2
              pq4 = insert 3 pq3
           in assertEqual "Should return minimum after multiple insertions" (findMin pq4) (Just 3)
      , testCase "Merge two BinomialHeaps" $
          let pq1 = insert 3 (insert 7 empty) :: BinomialHeap Int
              pq2 = insert 2 (insert 8 empty) :: BinomialHeap Int
              merged = merge pq1 pq2
           in assertEqual "Should return minimum from merged heaps" (findMin merged) (Just 2)
      , testCase "SplitMin on BinomialHeap" $
          let pq = insert 3 (insert 1 (insert 5 empty)) :: BinomialHeap Int
           in case splitMin pq of
                EmptyView -> assertFailure "SplitMin should not return EmptyView for non-empty heap"
                Min minVal restHeap -> do
                  assertEqual "Should extract minimum value" 1 minVal
                  assertEqual "Remaining heap should have correct minimum" (findMin restHeap) (Just 3)
      , testCase "SplitMin on empty BinomialHeap" $
          let pq = empty :: BinomialHeap Int
           in case splitMin pq of
                EmptyView -> return () -- This is expected
                Min _ _ -> assertFailure "SplitMin should return EmptyView for empty heap"
      , testCase "Multiple operations on BinomialHeap" $
          let pq1 = insert 5 (insert 2 (insert 8 empty)) :: BinomialHeap Int
              pq2 = insert 1 (insert 6 empty) :: BinomialHeap Int
              merged = merge pq1 pq2
           in case splitMin merged of
                EmptyView -> assertFailure "Should not be empty after merge"
                Min minVal restHeap -> do
                  assertEqual "Should extract global minimum" 1 minVal
                  assertEqual "Next minimum should be correct" (findMin restHeap) (Just 2)
    ]
