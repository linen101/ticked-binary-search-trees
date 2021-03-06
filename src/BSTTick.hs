{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}


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

{-@ type NEBST k v = {t: BST k v | 0 < size t } @-}


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
{-@ height :: t: Tree k v -> {n:Nat | n <= size t} @-}
height :: Tree k v -> Int
height Nil            = 0
height (Node k v l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}


-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect isEmpty @-}
isEmpty :: Tree k v -> Bool
isEmpty Nil = True
isEmpty _   = False

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
get k' (Node k v l r)
    | k' < k     = step 1 (get k' l)
    | k' > k     = step 1 (get k' r)
    | otherwise  = wait (Just v)

{-@ reflect delete @-}
{-@ delete :: Ord k => k:k -> ts:BST k v ->
              { t:Tick { ts':(BST k v)
                       | size ts' == size ts - 1 || size ts' == size ts }
              | tcost t <= height ts } @-}
delete :: Ord k => k -> Tree k v -> Tick (Tree k v)
delete _ Nil = pure Nil
delete k' t@(Node k v l r)
    | k' < k    = pure (\l' -> Node k v l' r) </> (delete k' l)
    | k' > k    = pure (\r' -> Node k v l r') </> (delete k' r)
    | otherwise = (deleteI t)

{-@ reflect deleteI @-}
{-@ deleteI :: Ord k => ts: NEBST k v ->
               { t:Tick { ts':(BST k v)
                        | size ts' == size ts - 1  }
               | tcost t <= height ts } @-}
deleteI :: Ord k => Tree k v -> Tick (Tree k v)
deleteI (Node _ _ Nil Nil) = pure Nil
deleteI (Node _ _ l Nil)   = pure l
deleteI (Node _ _ Nil r)   = pure r
deleteI (Node _ _ l r)     = pure f </> delMinKey2 r
  where f (v, k, r') = Node k v l r'

------------------------------------------------------------------------------
-- | delMinKey using user defined datatype MinKey:
-------------------------------------------------------------------------------  

{-@ data MinKey k v = MinKey { mkv_key  :: k
                             , mkv_val  :: v
                             , mkv_tree :: BST {x:k | mkv_key < x} v }
@-}
data MinKey k v = MinKey { mkv_key :: k
                         , mkv_val :: v
                         , mkv_tree :: Tree k v }

{-@ reflect delMinKey @-}
{-@ delMinKey :: Ord k => ts:NEBST k v ->
            { t:Tick { m:(MinKey k v) | size (mkv_tree m) == size ts - 1 }
            | tcost t <= height ts } @-}
delMinKey :: Ord k => Tree k v -> Tick (MinKey k v)
delMinKey (Node k v Nil r) = pure (MinKey k v r)
delMinKey (Node k v l r)   = pure f </> delMinKey l
  where f (MinKey k' v' l') = MinKey k' v' (Node k v l' r)


------------------------------------------------------------------------------
-- | delMinKey1 using user defined Ordered Tuple with abstract refinements:
-------------------------------------------------------------------------------  

{-@ data Triple k v <p :: mink:k -> x:k -> Bool> 
        = Triple { t_k :: k
                 , t_v :: v
                 , t_b :: BST k<p t_k> v
                 }
@-}

data Triple k v = Triple { t_k :: k
                         , t_v :: v
                         , t_b :: Tree k v 
                         } 

{-@ type OTriple = Triple <{\mink x -> mink < x}> k v @-}                       

{-@ reflect delMinKey1 @-}
{-@ delMinKey1 :: Ord k => ts:NEBST k v ->
            { t:Tick { o: OTriple | size (t_b o) == size ts - 1 }
            | tcost t <= height ts } @-}
delMinKey1 :: Ord k => Tree k v -> Tick (Triple k v)
delMinKey1 (Node k v Nil r) = pure (Triple k v r)
delMinKey1 (Node k v l r)   = pure f </> delMinKey1 l
  where f (Triple k' v' l') = Triple k' v' (Node k v l' r)

------------------------------------------------------------------------------
-- | delMinKey2 using abstract refinement on function type:
-------------------------------------------------------------------------------  

{-@ reflect delMinKey2 @-}
{-@ delMinKey2 :: Ord k => ts:NEBST k v ->
            { t:Tick (v, k, {ts':(BST k v) | size ts' == size ts - 1})
                     < \_ -> {k:k | true}
                     , \key -> {t:Tree {k:k | key < k} v | true} >
            | tcost t <= height ts } @-}
delMinKey2 :: Ord k => Tree k v -> Tick (v, k, Tree k v)
delMinKey2 (Node k v Nil r) = pure (v, k, r)
delMinKey2 (Node k v l r)   = pure (\(v', k', l') -> (v', k', Node k v l' r)) </> delMinKey2 l

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

{-@ ple delMinKeyCost @-}

{-@ delMinKeyCost :: Ord k => b:NEBST k v ->
               { tcost (delMinKey b) <= height b }
               / [height b] @-}
delMinKeyCost :: Ord k => Tree k v -> Proof
delMinKeyCost b@(Node k v Nil r)
    =   tcost (delMinKey2 b)
    ==. tcost (pure (v, k, r))
    ==. 0
    <=. height b
    *** QED

delMinKeyCost b@(Node k v l r)
    =   tcost (delMinKey2 b)
    ==. tcost (pure (\(v', k', l') -> (v', k', Node k v l' r)) </> delMinKey2 l)
    ==. 1 + tcost (delMinKey2 l)
        ? delMinKeyCost l
    <=. 1 + height l
    <=. height b
    *** QED

{-@ ple deleteICost @-}

{-@ deleteICost :: Ord k => b:NEBST k v ->
               { tcost (deleteI b) <= height b }
               / [height b] @-}
deleteICost :: Ord k => Tree k v -> Proof
deleteICost b@(Node _ _ Nil Nil)
    = tcost (deleteI b)
    ==. tcost (pure Nil)
    ==. 0
    <=. height b
    *** QED

deleteICost b@(Node _ _ l Nil)
    = tcost (deleteI b)
    ==. tcost (pure l)
    ==. 0
    <=. height b
    *** QED

deleteICost b@(Node _ _ Nil r)
    = tcost (deleteI b)
    ==. tcost (pure r)
    ==. 0
    <=. height b
    *** QED

deleteICost b@(Node _ _ l r)
    = tcost (deleteI b)
    ==. tcost (pure f </> delMinKey2 r)
    ==. 1 + tcost (delMinKey2 r)
       ? delMinKeyCost r
    <=. 1 + height r
    <=. height b
    *** QED
  where f (v, k, r') = Node k v l r'

{-@ deleteCost :: Ord k => key:k -> b:BST k v ->
               { tcost (delete key b) <= height b }
               / [height b] @-}
deleteCost :: Ord k => k -> Tree k v -> Proof
deleteCost key b@(Nil)
    =   tcost (delete key b)
    ==. tcost (pure Nil)
    ==. 0
    ==. height b
    <=. height b
    *** QED

deleteCost key b@(Node k v l r) | key == k
    =   tcost (delete key b)
    ==. tcost (deleteI b)
       ? deleteICost b
    <=. height b
    *** QED

deleteCost key b@(Node k v l r) | key < k
    =   tcost (delete key b)
    ==. tcost (pure (\l' -> Node k v l' r) </> delete key l)
    ==. 1 + tcost (delete key l)
        ? deleteCost key l
    <=. 1 + height l
    <=. height b
    *** QED

deleteCost key b@(Node k v l r) | key > k
    =   tcost (delete key b)
    ==. tcost (pure (\r' -> Node k v l r') </> delete key r)
    ==. 1 + tcost (delete key r)
        ? deleteCost key r
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

--- Using String does not work, let's figure out why!!!
--- Cannot unify [Char] with GHC.Base.String

{-@ t' :: BST Int [Char] @-}
t' :: Tree Int [Char]
t' = tval (set (tval (set (tval (set Nil 10 "kitty")) 20 "cat")) 30 "kitten")

{-@ test1' :: TT @-}
test1' :: Bool
test1' = tcost (get 10 t') <= height t'

{-@ test2' :: TT @-}
test2' :: Bool
test2' = tcost (set t' 40 "gato") <= height t'
