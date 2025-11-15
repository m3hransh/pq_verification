module Main where

import ExampleTests
import PriorityQueue.BinomialHeapTests
import PriorityQueue.LeftistHeapTests
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ -- leftistHeapTests
      exampleTests,
      binomialHeapTests
    ]
