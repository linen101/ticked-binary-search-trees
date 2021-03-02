{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module RBTdeletion where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, log, fmap, (=<<))
import Log2
import RBTree(Color(..),RBTree(..), Maybe(..), height, size, isB, bh, rh, isBH, isRB, col, isARB, isRBH, left, right, balanceR, balanceL, height_costUB)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

{-@ type ORBTN k v N = {v: ORBT k v  | bh v = N }         @-}

-------------------------------------------------------------------------------
-- Color change -------------------------------------------------------
-------------------------------------------------------------------------------

-- reduce the black height of the subtree c by reddening the node. 
-- This operation should only be called on BlackRBT. 
-- Here, c must be black because it is the child of a red node, 
-- and we know that c can't be Nil because it must have the same black height as (Node B y yv a b).

{-@ reflect makeRed @-}
{-@ makeRed :: t  : BlackRBT k v
            -> {t' : ARBTN k v {bh t - 1} | size t' > 0 && IsR t'} 
@-}
makeRed (Node _ k v l r) = Node R k v l r 

{-@ reflect makeBlackD @-}
{-@ makeBlackD :: t  : ARBT k v 
               -> {t' : RBT k v | (size t' = 0 || IsBlackRBT t' ) }
@-}
makeBlackD Nil              = Nil
makeBlackD (Node _ k v l r) = Node B k v l r 

-------------------------------------------------------------------------------
-- Delete -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect delete @-}
{-@ delete :: Ord k => k 
                    -> t : RBT k v 
                    -> {ti : Tick  {t' : (RBT k v) | (size t' = 0 || IsBlackRBT t') }
                           | tcost ti <= height t}  
@-}
delete k t = fmap makeBlackD (del k t)

-- termination -> decreasing parameter height t
{-@ reflect del @-}
{-@ del :: Ord k => k 
           -> t : RBT k v 
           -> { ti : Tick {t' : (ARBT k v) | (if (IsB t && size t>0) then bh t' = bh t - 1 else bh t' = bh t ) 
                            && (not (IsB t) => isRB t') }
                   | tcost ti <= height t }
           / [height t]
@-}
del :: Ord k => k -> RBTree k v -> Tick (RBTree k v)
del k Nil                   = pure Nil
del k (Node col key v l r) 
    | k < key   = case l of
            Nil            -> wait (Node R key v Nil r)
            Node B _ _ _ _ -> step 1 $ eqBind 0 (del k l) (\l' -> balL key v l' r)  
            _              -> pure (\l' -> Node R key v l' r) </> (del k l) 
    | k > key   = case r of
                Nil            -> wait (Node R key v l Nil)
                Node B _ _ _ _ -> step 1 $ eqBind 0 (del k r) (\r' -> balR key v l r')
                _              -> pure (\r' -> Node R key v l r') </> (del k r)
    | otherwise  = step 1 (merge k l r)

-------------------------------------------------------------------------------
-- Rotations -------------------------------------------------------
-------------------------------------------------------------------------------

-- 	Rebalancing function 
--  after a deletion from a left subtree 
--  of a black rooted tree
--  invariant bh t = bh l + 1

{-@ reflect balL @-}
{-@ balL :: Ord k => k:k -> v 
         -> l : ARBT {key:k | key < k} v  
         -> r : RBTN {key:k | key > k} v {bh l+1} 
         -> t' : { Tick {t : (ARBTN k v {bh l + 1}) | IsB r => isRB t}
                 | tcost t' == 0 }
@-}
balL :: Ord k => k -> v -> RBTree k v -> RBTree k v -> Tick (RBTree k v)
balL y yv (Node R x xv a b) c                  = pure ( Node R y yv (Node B x xv a b) c )
balL x xv bl r@(Node B _ _ _ _)                = balanceR x xv bl (makeRed r)  
balL x xv bl (Node R z zv (Node B y yv a b) c) = pure (\r -> Node R y yv (Node B x xv bl a) r ) <*> (balanceR z zv b (makeRed c))

-- 	Rebalancing function 
--  after a deletion from a right subtree 
--  of a black rooted tree
--  invariant bh t = bh l

{-@ reflect balR @-}
{-@ balR :: Ord k => k:k -> v 
         -> l : RBT {key:k | key < k} v  
         -> r : ARBTN {key:k | key > k} v {bh l - 1} 
         -> t' : { Tick { t : (ARBTN k v {bh l}) | IsB l => isRB t } 
                        | tcost t' == 0 }
@-} 
balR :: Ord k => k -> v -> RBTree k v -> RBTree k v -> Tick (RBTree k v)
balR x xv a (Node R y yv b c)                  = pure ( Node R x xv a (Node B y yv b c) )
balR y yv l@(Node B _ _ _ _) bl                = balanceL y yv (makeRed l) bl 
balR z zv (Node R x xv a (Node B y yv b c)) bl = pure ( \l -> Node R y yv l (Node B z zv c bl) ) <*> (balanceL x xv (makeRed a) b)

-------------------------------------------------------------------------------
-- Merge -------------------------------------------------------
-------------------------------------------------------------------------------

-- merge 2 trees 
-- with same bh

{-@ reflect merge @-}
{-@ merge :: Ord k => k:k 
          -> l : RBT {key:k | key < k} v 
          -> r : RBTN {key:k | key > k} v {bh l}
          -> {ti : Tick {t : (ARBTN k v {bh l}) | IsB l && IsB r => isRB t} 
                 | tcost ti <= min (height l) (height r) }
@-}
merge :: Ord k => k -> RBTree k v -> RBTree k v -> Tick (RBTree k v)
merge _ Nil x                               =  pure x
merge _ x Nil                               =  pure x
merge k (Node R x xv a b) (Node R y yv c d) =  pure (\m -> mergeR m) </> (merge k b c)
    where
        mergeR (Node R z zv b' c')  = (Node R z zv (Node R x xv a b') (Node R y yv c' d))
        mergeR bc                   = (Node R x xv a (Node R y yv bc d))
merge k (Node B x xv a b) (Node B y yv c d) = step 1 $ eqBind 0 (merge k b c) (\m -> mergeB m) 
    where
        mergeB (Node R z zv b' c')  = pure ( Node R z zv (Node B x xv a b') (Node B y yv c' d) )
        mergeB bc                   = (balL x xv a (Node B y yv c d))
merge k a (Node R x xv b c)                 =  pure (\l' -> Node R x xv l' c) <*> (merge k a b)    -- IsB l && IsB r => isRB t
merge k (Node R x xv a b) c                 =  pure (\r' -> Node R x xv a r') <*> (merge k b c)     -- IsB l && IsB r => isRB t   		
    
-------------------------------------------------------------------------------
-- Cost Proof -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ ple delete_costUB @-}
{-@ delete_costUB
    :: Ord k
    => k : k
    -> t : BlackRBT k v
    -> { tcost (delete k t) <= 2 * log (size t + 1) } 
    / [height t]
@-} 
delete_costUB :: Ord k => k -> RBTree k v -> Proof
delete_costUB k t 
    =   tcost (delete k t)
    <=. height t
      ? height_costUB t
    <=. 2 * log (size t + 1)  
    *** QED   

-------------------------------------------------------------------------------
-- Auxiliary Invariants -------------------------------------------------------
-------------------------------------------------------------------------------
{-@ predicate IsBlackRBT T =  bh T > 0 && IsB T @-}

{-@ predicate Inv1 T = (isARB T && IsB T) => isRB T @-}
{-@ predicate Inv2 T = isRB T => isARB T            @-}

{-@ using (Color) as {v: Color | v = R || v = B}              @-}
{-@ using (RBTree k v) as {t: RBTree k v | Inv1 t && Inv2 t}  @-}



