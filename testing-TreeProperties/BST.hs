{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-} 
{-@ LIQUID "--diff" @-} 

module BST  ( BSTree, Maybe, height, size, insert, lookup) where

import Prelude hiding ( Maybe(Nothing,Just),lookup, max, min, pure, return)
import Functions_Types (max, min, Nat, Maybe(Nothing,Just))
import Language.Haskell.Liquid.ProofCombinators

{-@ type NEBSTree k v = {t: BSTree k v | 0 < size t} @-}

{-@ data BSTree k v = Nil
                    | Node { tkey :: k
                           , tval :: v
                           , tleft :: BSTree {key:k  | key < tkey } v
                           , tright :: BSTree {key:k | key > tkey } v
                           }
  @-}

data BSTree k v = Nil | Node k v (BSTree k v) (BSTree k v) deriving Show

{-@ reflect empty @-}
{-@ empty :: {tr:(BSTree k v) | size tr == 0} @-}
empty :: BSTree k v
empty = Nil


{-@ reflect singleton @-}
{-@ singleton :: k -> v -> {t: BSTree k v | size t == 1 }@-}
singleton k v = Node k v Nil Nil

{-@ measure size @-}
{-@ size :: BSTree k v -> Nat @-}
size                :: BSTree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:BSTree k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: BSTree k v -> Nat @-}
height :: BSTree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:BSTree k v | 0 <= height t} @-}

{-@ reflect insert @-}
{-@ insert :: Ord k => t:BSTree k v-> k -> v -> { t': BSTree k v | size t' = size t || size t' = size t + 1} @-}
insert :: Ord k => BSTree k v-> k -> v -> BSTree k v
insert Nil k v  = singleton k v
insert (Node k v l r) k' v'
    | k' < k    =  Node k v (insert l k' v') r
    | k' > k    =  Node k v l (insert r k' v')
    | otherwise =  Node k' v' l r


{-@ reflect lookup @-}
{-@ lookup :: (Ord k) =>  t: BSTree k v -> k:k -> Maybe v @-}
lookup Nil k    = Nothing
lookup (Node k v l r) k'
    | k' < k    = lookup l k'
    | k' > k    = lookup r k'
    | otherwise = Just v

{-@ lem_lookup_eq :: (Ord k) => tree:(BSTree k v) -> key:k -> val:v -> 
      { lookup (insert tree key val) key = Just val }
  @-}
lem_lookup_eq :: (Ord k) => BSTree k v -> k -> v -> Proof
lem_lookup_eq Nil _ _ = ()
lem_lookup_eq (Node k v l r) key val
    | key == k        = () 
    | key <  k        = lem_lookup_eq l key val
    | otherwise       = lem_lookup_eq r key val

{-@ lem_lookup_neq :: (Ord k) => tree:(BSTree k v) -> k1:k -> k2:{ k2 /= k1 } -> val:v -> 
      { lookup (insert tree k2 val) k1 = lookup tree k1  }
  @-}
lem_lookup_neq :: (Ord k) => BSTree k v -> k -> k -> v -> Proof
lem_lookup_neq Nil k1 k2 _  
    | k1 < k2             = ()
    | otherwise           = ()
lem_lookup_neq (Node k v l r) k1 k2 v' 
    | k1 <  k, k  < k2    = () 
    | k  == k2            = () 
    | k1 == k, k  < k2    = () 
    | k2 <  k, k == k1    = () 
    | k2 <  k, k  < k1    = ()
    | k1 < k, k2 < k      = lem_lookup_neq l k1 k2 v'
    | k < k1, k < k2      = lem_lookup_neq r k1 k2 v'



-------------------------------------------------------------------------------
-- | example BSTree | ---------------------------------------------------------
{-@ reflect exTree @-}
exTree :: () -> BSTree Int String 
exTree _ = insert (insert (insert Nil 10 "cat") 20 "dog") 30 "zebra"

{-@ propOK :: () -> TT @-}
propOK :: () -> Bool 
propOK () = lookup ex 10 == Just "cat" 
         && lookup ex 20 == Just "dog"
         && lookup ex 30 == Just "zebra"
         && lookup ex 0  == Nothing
  where 
    ex    = exTree ()








