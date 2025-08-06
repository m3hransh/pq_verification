module PriorityQueue.Base where

{-@ data MinView q a =
        EmptyView
      | Min { minValue :: a, restHeap :: q a }
  @-}
data MinView q a = EmptyView | Min {minValue :: a, restHeap :: q a}
  deriving (Show, Eq)

class PriorityQueue pq where
  empty :: (Ord a) => pq a
  isEmpty :: (Ord a) => pq a -> Bool
  insert :: (Ord a) => a -> pq a -> pq a
  splitMin :: (Ord a) => pq a -> MinView pq a
