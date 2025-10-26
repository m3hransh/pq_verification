{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ExampleTests where

import Control.Exception (SomeException, try)
import Example
import Language.Haskell.Liquid.ProofCombinators
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
    ]
