module PriorityQueue.LeftistHeapTests where

-- import PriorityQueue.LeftistHeap
-- import Test.Tasty
-- import Test.Tasty.HUnit
--
-- leftistHeapTests :: TestTree
-- leftistHeapTests =
--   testGroup
--     "LeftistHeap"
--     [ testCase "Add one element to heap" $
--         let heap = empty :: LeftistHeap Int
--             heap' = insert 5 heap
--          in assertEqual "Heap should contain the element" (splitMin heap') (Min 5 EmptyHeap)
--     , testCase "Add and remove elements" $
--         let heap = insert 3 $ insert 2 $ insert 5 (empty :: LeftistHeap Int)
--          in assertEqual "Heap" (minValue $ splitMin $ restHeap $ splitMin heap) (3)
--     ]
