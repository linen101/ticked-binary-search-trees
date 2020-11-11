module Functions_Types (max, min, Nat, Maybe(Nothing,Just)) where

import Prelude hiding ( Maybe(Nothing,Just),lookup, max, min, pure, return)

{-@ inline max @-}
max :: Ord a =>  a-> a ->  a
max x y = if x > y then x else y

{-@ inline min @-}
min :: Ord a => a ->  a -> a
min x y = if x > y then y else x

{-@ type Nat = {v:Int | 0 <= v} @-}
type Nat = Int

data Maybe a = Just a | Nothing   
    deriving (Eq, Ord)
