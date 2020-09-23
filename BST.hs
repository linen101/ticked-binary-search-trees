module BST  ( BSTree, Maybe, height, size, insert, lookup) where

import Prelude hiding ( Maybe(Nothing,Just),lookup, max, min,)

{-@ inline max @-}
max :: Ord a =>  a-> a ->  a
max x y = if x > y then x else y

{-@ inline min @-}
min :: Ord a => a ->  a -> a
min x y = if x > y then y else x

{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ type NEBSTree a = {t: BSTree a | 0 < size t} @-}

{-@ data BSTree k v = Nil
                    | Node { tkey :: k
                           , tval :: v
                           , tleft :: BSTree {key:k  | key < tkey } v
                           , tright :: BSTree {key:k | key > tkey } v
                           }
  @-}

data Maybe a = Just a | Nothing   

data BSTree k v = Nil | Node k v (BSTree k v) (BSTree k v) deriving Show

{-@ empty :: {t: BSTree k v | size t == 0} @-}
empty = Nil

{-@ singleton :: k -> v -> {t: BSTree k v | size t == 1 }@-}
singleton k v = Node k v Nil Nil

{-@ measure size @-}
{-@ size :: BSTree k v -> Nat @-}
size                :: BSTree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: BSTree k v -> Nat @-}
height :: BSTree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}

{-@ insert :: Ord k => t:BSTree k v-> k -> v -> { t': BSTree k v | size t' = size t || size t' = size t + 1} @-}
insert :: Ord k => BSTree k v-> k -> v -> BSTree k v
insert Nil k v  = singleton k v
insert (Node k v l r) k' v'
    | k' < k    =  Node k v (insert l k' v') r
    | k' > k    =  Node k v l (insert r k' v')
    | otherwise =  Node k v' l r

{-@ lookup :: (Ord k) =>  t: BSTree k v -> k:k -> Maybe v @-}
lookup Nil k    = Nothing
lookup (Node k v l r) k'
    | k' < k    = lookup l k'
    | k' > k    = lookup r k'
    | otherwise = Just v







