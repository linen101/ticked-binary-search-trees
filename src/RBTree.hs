{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}


module RBTree (RBTree(..), Maybe(..), height, size) where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, fmap)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators

-------------------------------------------------------------------------------
-- | Datatypes:
-------------------------------------------------------------------------------

{-@ data RBTree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool>
        = Nil
        | Node { col :: Color
               , key :: k
               , val :: v
               , tl  :: RBTree <l, r> (k <l key>) v
               , tr  :: RBTree <l, r> (k <r key>) v }
@-}

data RBTree k v = Nil | Node Color k v (RBTree k v) (RBTree k v) deriving Show

data Color = R | B deriving (Eq,Show)

{-@ type ORBT k v = RBTree <{\root k -> k < root}, {\root k -> k > root}> k v @-}

{-@ type NERB k v = {t: RBTree k v | 0 < size t} @-}

{-@ type NERBT k v = {t: ORBT k v | 0 < size t } @-}

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

--  size invariant  --  

{-@ measure size @-}
{-@ size :: RBTree k v -> Nat @-}
size :: RBTree k v -> Int
size Nil             = 0
size (Node _ _ _ l r) = 1 + size l + size r
{-@ invariant {t:RBTree k v | 0 <= size t} @-}

--  height invariant   --

{-@ measure height @-}
{-@ height :: RBTree k v -> Nat @-}
height :: RBTree k v -> Int
height Nil              = 0
height (Node _ _ _ l r) = 1 + max (height l) (height r)
{-@ invariant {t:RBTree k v | 0 <= height t} @-}

--	black rooted Tree 	--

{-@ measure isB @-}
{-@ isB :: RBTree k v -> Bool @-}
isB :: RBTree k v -> Bool
isB Nil              = True
isB (Node B _ _ _ _) = True
isB (Node R _ _ _ _) = False

--	color invariant	--

{-@ measure isRB @-}
{-@ isRB :: RBTree k v -> Bool @-}
isRB :: RBTree k v -> Bool
isRB Nil              = True
isRB (Node B _ _ l r) = isRB l
                     && isRB r
isRB (Node R _ _ l r) = isRB l
                     && isRB r
                     && isB l   
                     && isB r

{-@ measure almostRB @-}
{-@ almostRB :: RBTree k v -> Bool @-}
almostRB :: RBTree k v -> Bool
almostRB Nil              = True
almostRB (Node _ _ _ l r) = isRB l
                         && isRB r

{-@ measure blackh @-}
{-@ blackh :: RBTree k v -> Nat @-}
blackh :: RBTree k v -> Int
blackh Nil              = 0
blackh (Node R _ _ l _) = blackh l
blackh (Node B _ _ l _) = blackh l + 1


