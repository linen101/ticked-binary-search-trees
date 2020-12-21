{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}


module RBTree (Tree(..), Maybe(..), height, size) where

import Functions_Types (max, min, Nat, Maybe(..))
import Prelude hiding (Applicative(..), Monad(..), Maybe(..), max, min, fmap)

import Language.Haskell.Liquid.RTick
import Language.Haskell.Liquid.RTick.Combinators


data Tree k v = Nil | Node Color k v !(Tree k v) !(Tree k v) deriving Show

data Color = R | B deriving (Eq,Show)

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

--  size invariant  --  

{-@ measure size @-}
{-@ size :: Tree k v -> Nat @-}
size :: Tree k v -> Int
size Nil             = 0
size (Node _ _ _ l r) = 1 + size l + size r
{-@ invariant {t:Tree k v | 0 <= size t} @-}

--  height invariant   --

{-@ measure height @-}
{-@ height :: Tree k v -> Nat @-}
height :: Tree k v -> Int
height Nil              = 0
height (Node _ _ _ l r) = 1 + max (height l) (height r)
{-@ invariant {t:Tree k v | 0 <= height t} @-}



-------------------------------------------------------------------------------
-- | Datatypes:
-------------------------------------------------------------------------------

{-@ data Tree k v <l :: root:k -> x:k -> Bool, r :: root:k -> x:k -> Bool>
        = Nil
        | Node { tcol :: Color
               , key :: k
               , val :: v
               , tl  :: Tree <l, r> (k <l key>) v
               , tr  :: Tree <l, r> (k <r key>) v }
@-}

--      Ordered Trees       --

{-@ type ORBT k v = Tree <{\root k -> k < root}, {\root k -> k > root}> k v @-}                           

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ makeBlack :: ORBT k v -> ORBT k v @-}
makeBlack :: Tree k v -> Tree k v
makeBlack Nil = Nil
makeBlack (Node _ k v l r) = Node B k v l r

{-@ set :: k -> v -> ORBT k v -> ORBT k v @-}
set k v t = makeBlack (insert k v t)


{-@ insert :: Ord k => k -> v -> ORBT k v -> ORBT k v @-}
insert k v Nil = Node B k v Nil Nil
insert k v t@(Node c key val l r)
    | k < key   = balanceL c key val (insert k v l) r
    | k > key   = balanceR c key val l (insert k v r)
    | otherwise = t

{-@ balanceL :: Color -> k:k -> v -> ORBT {key:k | key < k} v -> ORBT {key:k | key > k} v -> ORBT k v @-}
balanceL B z zv (Node R y yv (Node R x xv a b) c) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL c k v l r = Node c k v l r

{-@ balanceR :: Color -> k:k -> v -> ORBT {key:k | key < k} v -> ORBT {key:k | key > k} v -> ORBT k v @-}
balanceR B y yv (Node R x xv a b) (Node R z zv c d) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR col y yv x (Node R z zv c d) = Node col z zv (Node R y yv x c) d
balanceR col x xv a b = Node col x xv a b