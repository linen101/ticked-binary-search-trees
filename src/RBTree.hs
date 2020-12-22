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


--  check if root is black  --

{-@ measure isB @-}
{-@ isB :: Tree k v -> Bool @-}
isB :: Tree k v -> Bool  
isB Nil = True
isB (Node c _ _ _ _) = c == B

--  black height of tree  --
-- blackh only considers the left sub-tree, 
-- but this is legitimate, because isBH will ensure the
-- right subtree has the same blackh.

{-@ measure blackh @-}
{-@ blackh :: Tree k v -> Nat @-}
blackh :: Tree k v -> Int 
blackh Nil = 0
blackh (Node c _ _ l r) = blackh l + if c == B then 1 else 0

-- `black height invariant `--
{-@ measure isBH @-}
{-@ isBH :: Tree k v -> Bool @-}
isBH :: Tree k v -> Bool
isBH Nil = True
isBH (Node c _ _ l r) = blackh l == blackh r
                     && isBH l 
                     && isBH r

--    color invariant   --

{-@ measure isAlmostRB @-}
{-@ isAlmostRB :: Tree k v -> Bool @-}
isAlmostRB :: Tree k v -> Bool
isAlmostRB Nil = True
isAlmostRB (Node c _ _ l r) = isAlmostRB l && isAlmostRB r

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

--      Red-Black Trees     --

{-@ type RBT k v = {t:ORBT k v | isBH t && isAlmostRB t} @-}

{-@ type RBTN k v N = {t:RBT k v | (blackh t) = N} @-}                          

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ makeBlack :: RBT k v -> RBT k v @-}
makeBlack :: Tree k v -> Tree k v
makeBlack Nil = Nil
makeBlack (Node _ k v l r) = Node B k v l r

{-@ set :: k -> v -> RBT k v -> RBT k v @-}
set k v t = makeBlack (insert k v t)


{-@ insert :: Ord k => k -> v -> t: RBT k v -> RBTN k v {(blackh t)} @-}
insert k v Nil = Node R k v Nil Nil
insert k v t@(Node B key val l r)
    | k < key   = balanceL key val (insert k v l) r
    | k > key   = balanceR key val l (insert k v r)
    | otherwise = t
insert k v t@(Node R key val l r)
    | k < key   = Node R key val (insert k v l) r
    | k > key   = Node R key val l (insert k v r)
    | otherwise = t


{-@ balanceL ::  k:k -> v -> l:RBT {key:k | key < k} v -> RBTN {key:k | key > k} v {(blackh l)} -> RBTN k v {1+ (blackh l)} @-}
balanceL z zv (Node R y yv (Node R x xv a b) c) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL z zv (Node R x xv a (Node R y yv b c)) d = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceL k v l r = Node B k v l r

{-@ balanceR :: k:k -> v -> l:RBT {key:k | key < k} v -> RBTN {key:k | key > k} v {(blackh l)} -> RBTN k v {1+ (blackh l)} @-}
balanceR x xv a (Node R y yv b (Node R z zv c d)) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR x xv a (Node R z zv (Node R y yv b c) d) = Node R y yv (Node B x xv a b) (Node B z zv c d)
balanceR x xv a b = Node B x xv a b