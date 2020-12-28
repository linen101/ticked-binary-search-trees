
module Log2 where

import Language.Haskell.Liquid.RTick.Combinators

assumption = () 
--
-- Define an abstract measure called 'log'
-- LH knows nothing about its implementation
--
{-@ measure log :: a -> a @-}

--
-- log_2 rounded to the nearest integer
--
{-@ assume log :: x:Int -> {v:Int | v == log x } @-}
log :: Int -> Int
log x = round (logBase 2 (fromIntegral x))

--
-- Assume that log_2 1 == 0
--
{-@ assume logOne :: { log 1 == 0 } @-}
logOne :: Proof
logOne  = assumption
--
-- Assume that log_2 == 1
--
{-@ assume logTwo :: { log 2 == 1 } @-}
logTwo :: Proof
logTwo  = assumption


{-@ assume logNat :: x:{ Int | 0 <= x } -> { 0 <= log x } @-}
logNat :: Int -> Proof
logNat _ = assumption

{-@ assume logPos :: x:{ Int | 1 < x } -> { 0 < log x } @-}
logPos :: Int -> Proof
logPos _ = assumption

--
-- Log ratio law: log_b (x / y) == log_b x - log_b y
--
{-@ assume logDiv :: x:Int -> y:Int -> {log (x / y) = log x - log y } @-}
logDiv :: Int -> Int -> Proof
logDiv _ _ = assumption

--
-- Log ratio law: log_b (x + y) == log_b x + log_b (1+y/x)
--
{-@ assume logPlus :: x:Int -> y:Int -> {log (x + y) = log x + log (1 + y/x) } @-}
logPlus :: Int -> Int -> Proof
logPlus _ _ = assumption

-------------------------------------------------------------------------------
-- | Powers of 2:
-------------------------------------------------------------------------------

{-@ measure p2 :: Nat -> Bool @-}

--
-- Given @2^k@, assume @2^(k + 1)@.
--
{-@ assume nextP2 :: { m:Nat | p2 m }
    -> { n:Nat | 2 * m == n && m == n / 2 && p2 n }
@-}
nextP2 :: Int -> Int
nextP2 m = 2 * m

--
-- Given @2^k@ where @k > 0@, assume @2^(k - 1)@.
--
{-@ assume prevP2 :: { m:Nat | m > 1 && p2 m }
    -> { n:Nat | m / 2 == n && m == 2 * n && p2 n }
@-}
prevP2 :: Int -> Int
prevP2 m = m `div` 2

--
-- Given @2^k@ where @k > 0@, assume @2^k@ is 'Even''.
--
{-@ p2Even :: { m:Nat | m > 1 && p2 m } -> { n:Even | m == n } @-}
p2Even :: Int -> Int
p2Even m = m
  ? toProof (prevP2 m)

--
-- 2^x
--
{-@ reflect twoToPower @-}
{-@ twoToPower :: Nat -> Nat @-}
twoToPower :: Int -> Int
twoToPower 0 = 1
twoToPower n = 2 * twoToPower (n - 1)
