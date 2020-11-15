{-@ LIQUID "--reflection" @-}

module BSTTick (Tree(..), Maybe(..), height, size, set, get) where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators


-------------------------------------------------------------------------------
-- | Datatype:
-------------------------------------------------------------------------------

{-@ data Tree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool>
        = Nil
        | Node { key :: k
               , val :: v
               , tl  :: Tree <l, r> (k <l key>) v
               , tr  :: Tree <l, r> (k <r key>) v }
@-}

data Tree k v = Nil | Node k v (Tree k v) (Tree k v) deriving Show

{-@ type BST k v = Tree <{\root k -> k < root}, {\root k -> k > root}> k v @-}
{-@ type NETree k v = {t: Tree k v | 0 < size t} @-}


-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

{-@ measure size @-}
{-@ size :: Tree k v -> Nat @-}
size :: Tree k v -> Int
size Nil            = 0
size (Node _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

{-@ measure height @-}
{-@ height :: Tree k v -> Nat @-}
height :: Tree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}


-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect empty @-}
{-@ empty :: { t:Tick { ts:(BST k v) | size ts == 0 } | tcost t == 0 } @-}
empty :: Tick (Tree k v)
empty = pure Nil

{-@ reflect singleton @-}
{-@ singleton :: k -> v ->
                 { t:Tick { ts:(BST k v) | size ts == 1 } | tcost t == 0 } @-}
singleton :: Ord k => k -> v -> Tick (Tree k v)
singleton k v = pure (Node k v Nil Nil)

{-@ reflect set @-}
{-@ set :: Ord k => ts:BST k v -> k -> v ->
           { t:Tick { ts':(BST k v)
                    | size ts' == size ts + 1 || size ts' == size ts }
           | tcost t <= height ts } @-}
set :: Ord k => Tree k v -> k -> v -> Tick (Tree k v)
set Nil k v = singleton k v
set (Node k v l r) k' v'
    | k' < k    = pure (\l' -> Node k v l' r) </> set l k' v'
    | k' > k    = pure (\r' -> Node k v l r') </> set r k' v'
    | otherwise = wait (Node k v' l r)

{-@ reflect get @-}
{-@ get :: Ord k => k:k -> ts: BST k v ->
         { t:Tick (Maybe v) | tcost t <= height ts } @-}
get :: Ord k => k -> Tree k v -> Tick (Maybe v)
get _ Nil    = pure Nothing
get key (Node k v l r)
    | key < k    = step 1 (get key l)
    | key > k    = step 1 (get key r)
    | otherwise  = wait (Just v)


-------------------------------------------------------------------------------
-- | Extrinsic cost proofs:
-------------------------------------------------------------------------------

{-@ getCost :: Ord k => key:k -> b:BST k v ->
               { tcost (get key b) <= height b }
               / [height b] @-}
getCost :: Ord k => k -> Tree k v -> Proof
getCost key b@(Nil)
   =   tcost (get key b)
   ==. tcost (pure Nothing)
   ==. tcost (Tick 0 Nothing)
   ==. 0
   <=. height b
   *** QED

getCost key b@(Node k v l r) | key == k
   =   tcost (get key b)
   ==. tcost (wait (Just v))
   ==. tcost (Tick 1 (Just v))
   ==. 1
   <=. height b
   *** QED

getCost key b@(Node k v l r) | key < k
   =   tcost (get key b)
   ==. tcost (step 1 (get key l))
   ==. 1 + tcost (get key l)
       ? getCost key l
   <=. 1 + height l
   <=. height b
   *** QED

getCost key b@(Node k v l r) | key > k
   =   tcost (get key b)
   ==. tcost (step 1 (get key r))
   ==. 1 + tcost (get key r)
       ? getCost key r
   <=. 1 + height r
   <=. height b
   *** QED


{-@ setCost :: Ord k => key:k -> val:v -> b:BST k v ->
               { tcost (set b key val) <= height b }
               / [height b] @-}
setCost :: Ord k => k -> v -> Tree k v -> Proof
setCost key val b@(Nil)
    =   tcost (set b key val)
    ==. tcost (singleton key val)
    ==. tcost (pure (Node key val Nil Nil))
    ==. 0
    ==. height b
    <=. height b
    *** QED

setCost key val b@(Node k v l r) | key == k
    =   tcost (set b key val)
    ==. tcost (wait (Node k val l r))
    ==. tcost (Tick 1 (Node k val l r))
    ==. 1
    <=. height b
    *** QED

setCost key val b@(Node k v l r) | key < k
    =   tcost (set b key val)
    ==. tcost (pure (\l' -> Node k v l' r) </> set l key val)
    ==. 1 + tcost (set l key val)
        ? setCost key val l
    <=. 1 + height l
    <=. height b
    *** QED

setCost key val b@(Node k v l r) | key > k
    =   tcost (set b key val)
    ==. tcost (pure (\r' -> Node k v l r') </> set r key val)
    ==. 1 + tcost (set r key val)
        ? setCost key val r
    <=. 1 + height r
    <=. height b
    *** QED


-------------------------------------------------------------------------------
-- | An example BST
-------------------------------------------------------------------------------
{-@ t :: BST Int Char @-}
t :: Tree Int Char
t = tval (set (tval (set (tval (set Nil 10 'c')) 20 'd')) 30 'z')

{-@ test1 :: TT @-}
test1 :: Bool
test1 = tcost (get 10 t) <= height t

{-@ test2 :: TT @-}
test2 :: Bool
test2 = tcost (set t 40 's') <= height t

{- This does not work, let's figure out why!!!
   Cannot unify [Char] with GHC.Base.String

{-@ t :: BST Int String @-}
t :: Tree Int String
t = tval (set (tval (set (tval (set Nil 10 "cat")) 20 "dog")) 30 "zebra")

{-@ test1 :: TT @-}
test1 :: Bool
test1 = tcost (get 10 t) <= height t

{-@ test2 :: TT @-}
test2 :: Bool
test2 = tcost (set t 40 "squirrel") <= height t

-}
