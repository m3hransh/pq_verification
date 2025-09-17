{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ExampleTests where

import qualified Example as Ex
import Test.Tasty
import Test.Tasty.HUnit
import Language.Haskell.Liquid.ProofCombinators
import Control.Exception (SomeException, try)

exampleTests :: TestTree
exampleTests =
  testGroup
    "Example"
    [ testCase "Lookup element in a list" $
        let list = [1, 2, 3, 4, 5]
         in assertEqual "Should return the element at the given index" (Ex.lookup 2 list) 3
    , testCase "Failed lookup in a list" $
        let list = [1, 2, 3, 4, 5]
         in assertEqual "Should return 2" (Ex.lookup 1 list) 2
    , testCase "Out of bound lookup" $
        let list = [1, 2, 3, 4, 5]
         in do
              result <- try (return (Ex.lookup 10 list)) :: IO (Either SomeException Int)
              case result of
                Left _ -> assertBool "" True
                Right _ -> assertFailure "Should have thrown an exception"
    ]