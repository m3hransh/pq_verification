module Main where

import PriorityQueue.LeftistHeapTests
import Test.Tasty
import Test.Tasty.HUnit


main :: IO ()
main = defaultMain leftistHeapTests
