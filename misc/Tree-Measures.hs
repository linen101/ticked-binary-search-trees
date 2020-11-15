module Measures (Tree(..), size, height, root, searchTree) where

import Prelude hiding (max, min)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ inline max @-}
max :: Ord a => a -> a -> a
max x y = if x > y then x else y

{-@ inline min @-}
min :: Ord a => a -> a -> a
min x y = if x > y then y else x

{-@ data Tree [size] k v = Nil
                         | Node { tkey :: k
                                , tval :: v
                                , tleft :: Tree k v
                                , tright :: Tree k v}
@-}

data Tree k v = Nil | Node k v (Tree k v) (Tree k v) deriving Show

{-@ measure size @-}
{-@ size :: Tree k v -> Nat @-}
size                :: Tree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: Tree k v -> Nat @-}
height :: Tree k v -> Int
height Nil                = 0
height (Node k v l r)
    | height l > height r = 1 + height l
    | otherwise           = 1 + height r
{-@ invariant {t:Tree k v | 0 <= height t} @-}

{-@ measure isempty @-}
isempty                :: (Tree k v) -> Bool
isempty Nil            = True
isempty _              = False

{-@ type NETree k v  = {t: Tree k v | not (isempty t)} @-}

{-@ measure root @-}
{-@ root :: NETree k v -> k @-}
root                :: Tree k v -> k
root (Node k _ _ _) = k

{-@ measure issingleton @-}
{-@ issingleton :: Tree k v -> Bool @-}
issingleton :: (Tree k v) -> Bool
issingleton (Node k v Nil Nil) = True
issingleton _                  = False

{-@ measure maxt @-}
{-@ maxt :: Ord k => NETree k v -> k @-}
maxt (Node k _ _ Nil) = k
maxt (Node _ _ _ r)   = maxt r

{-@ measure mint @-}
{-@ mint :: Ord k => NETree k v -> k @-}
mint (Node k _ Nil _) = k
mint (Node _ _ l _) = mint l

{-@ measure searchTree @-}
searchTree :: Ord k => Tree k v -> Bool
searchTree Nil                = True
searchTree (Node k _ Nil Nil) = True
searchTree (Node k _ l Nil)   = maxt l < k && searchTree l
searchTree (Node k _ Nil r)   = mint r > k && searchTree r
searchTree (Node k _ l r)     = maxt l < k
                             && mint r > k
                             && searchTree l
                             && searchTree r
