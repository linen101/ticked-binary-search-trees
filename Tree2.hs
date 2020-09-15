module Tree2 (Tree, Nat, NETree, height, size, root) where

{-@ type Nat = {v:Int | 0 <= v} @-}
type Nat = Int

{-@ type NETree a = {t: Tree a | 0 < size t} @-}
type NETree a = Tree a

{-@ data Tree [size] @-}
-- or: data Tree a = Nil | Node (x::a) (l::Tree a) (r::Tree a)
data Tree a = Nil | Node a (Tree a) (Tree a) deriving Show

{-@ measure height @-}
{-@ height :: Tree a -> Nat @-}
height :: Tree a -> Int
height Nil = 0
height (Node x l r) = 1 + max (height l) (height r)
{-@ invariant {v:Tree a | 0 <= height v} @-}

{-@ measure size @-}
{-@ size :: Tree a -> Nat @-}
size :: Tree a -> Int
size Nil = 0
size (Node x l r) = 1 + size l + size r
{-@ invariant {v:Tree a | 0 <= size v} @-}

{-@ silly_insert :: Eq a => t:Tree a -> x:a -> {t':Tree a | size t' == 1 + size t || size t' = size t}  @-}
silly_insert :: Eq a => Tree a -> a -> Tree a
silly_insert Nil x = Node x Nil Nil
silly_insert t@(Node y l r) x
    | x == y               =  t
    | height l > height r  =  Node y l (Node x r Nil)
    | otherwise            =  Node y (Node x l Nil) r

{-@ root :: NETree a -> a @-}
root :: Tree a -> a
root (Node x _ _) = x
