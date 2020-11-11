{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-} 
{-@ LIQUID "--diff" @-} 

module BST_AbstractRef  ( Tree, Maybe, height, size, set, get) where

import Prelude hiding ( Maybe(Nothing,Just), max, min, pure, return)
import Functions_Types (max, min, Nat, Maybe(Nothing,Just))
import Language.Haskell.Liquid.ProofCombinators

{-@ type NETree k v= {t: Tree k v | 0 < size t} @-}

{-@ data Tree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool> 
        = Nil
        | Node { key :: k
               , val :: v
               , tl  :: Tree <l, r> (k <l key>) v
               , tr  :: Tree <l, r> (k <r key>) v }
@-}

data Tree k v = Nil | Node k v (Tree k v) (Tree k v) deriving Show

{-@ type BST k v = Tree <{\root k -> k < root}, {\root k -> k > root}> k v @-}

{-@ reflect empty @-}
{-@ empty :: {tr:(BST k v) | size tr == 0} @-}
empty :: Tree k v
empty = Nil


{-@ reflect singleton @-}
{-@ singleton :: k -> v -> {t: BST k v | size t == 1 } @-}
singleton :: k -> v -> Tree k v
singleton k v = Node k v Nil Nil

{-@ measure size @-}
{-@ size :: BST k v -> Nat @-}
size                :: Tree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:BST k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: BST k v -> Nat @-}
height :: Tree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:BST k v | 0 <= height t} @-}

{-@ reflect set @-}
{-@ set :: Ord k => t:BST k v-> k -> v -> { t': BST k v | size t' = size t || size t' = size t + 1} @-}
set :: Ord k => Tree k v-> k -> v -> Tree k v
set Nil k v  = singleton k v
set (Node k v l r) k' v'
    | k' < k    =  Node k v (set l k' v') r
    | k' > k    =  Node k v l (set r k' v')
    | otherwise =  Node k' v' l r


{-@ reflect get @-}
{-@ get :: (Ord k) =>  t: BST k v -> k:k -> Maybe v @-}
get Nil k    = Nothing
get (Node k v l r) k'
    | k' < k    = get l k'
    | k' > k    = get r k'
    | otherwise = Just v

{-@ lem_get_eq :: (Ord k) => tree:(BST k v) -> key:k -> val:v -> 
      { get (set tree key val) key = Just val }
  @-}
lem_get_eq :: (Ord k) => Tree k v -> k -> v -> Proof
lem_get_eq Nil _ _ = ()
lem_get_eq (Node k v l r) key val
    | key == k        = () 
    | key <  k        = lem_get_eq l key val
    | otherwise       = lem_get_eq r key val

{-@ lem_get_neq :: (Ord k) => tree:(BST k v)-> k1:k -> k2:{ k2 /= k1 } -> val:v -> 
      { get (set tree k2 val) k1 = get tree k1  }
  @-}
lem_get_neq :: (Ord k) => Tree k v -> k -> k -> v -> Proof
lem_get_neq Nil k1 k2 _  
    | k1 < k2             = ()
    | otherwise           = ()
lem_get_neq (Node k v l r) k1 k2 v' 
    | k1 <  k, k  < k2    = () 
    | k  == k2            = () 
    | k1 == k, k  < k2    = () 
    | k2 <  k, k == k1    = () 
    | k2 <  k, k  < k1    = ()
    | k1 < k, k2 < k      = lem_get_neq l k1 k2 v'
    | k < k1, k < k2      = lem_get_neq r k1 k2 v'



-------------------------------------------------------------------------------
-- | example BST | ---------------------------------------------------------
{-@ reflect exTree @-}
{-@ exTree :: () -> BST Int String @-}
exTree :: () -> Tree Int String 
exTree _ = set (set (set Nil 10 "kitty") 20 "kitten") 30 "cat"

{-@ propOK :: () -> TT @-}
propOK :: () -> Bool 
propOK () = get ex 10 == Just "kitty" 
         && get ex 20 == Just "kitten"
         && get ex 30 == Just "cat"
         && get ex 0  == Nothing
  where 
    ex    = exTree ()