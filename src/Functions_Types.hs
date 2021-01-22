module Functions_Types (max, min, Nat, Maybe(..), Ordering(..), compare,logTwotoPower, logComp) where

import Language.Haskell.Liquid.RTick.Combinators
import Prelude hiding (Maybe(..), Ordering(..), lookup, max, min, compare, log, pure, return)
import Log2

{-@ inline max @-}
max :: Ord a => a -> a -> a
max x y = if x > y then x else y

{-@ inline min @-}
min :: Ord a => a -> a -> a
min x y = if x > y then y else x

{-@ inline compare @-}
compare x y = if x == y then EQ
              else if x <= y then LT
              else GT

{-@ assume logTwotoPower :: x : Nat 
                            -> { log (twoToPower x) == x } 
@-}
logTwotoPower :: Int -> Proof
logTwotoPower _ = assumption

{-@ assume logComp ::   x:Int -> y: Int 
                        -> { x <= y => log x <= log y } 
@-}
logComp :: Int -> Int -> Proof
logComp _ _ = assumption

{-@ type Nat = {v:Int | 0 <= v} @-}
type Nat = Int

data Maybe a = Just a | Nothing
    deriving (Eq, Ord)

data Ordering = LT | GT | EQ

