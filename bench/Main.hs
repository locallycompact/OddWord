{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module Main where

import Data.Proxy
import Data.Typeable
import Data.Word
import Data.Word.Odd
import Criterion.Main

testAddMul :: (Num a) => a -> a
testAddMul n = 2*n*n + 3*n + 4

testEquals :: (Eq a, Num a) => a -> Bool
testEquals n = n == 7 || n == 11 || n == 13

benchNum :: forall a. (Eq a, Num a, Typeable a) => a -> Benchmark
benchNum x =
    bgroup (show $ typeRep (Proxy :: Proxy a)) [
        bench "addMul" $ whnf testAddMul x,
        bench "equals" $ whnf testEquals x
    ]

main :: IO ()
main =
    defaultMain [
        benchNum (1::Word),
        benchNum (1::Word20),
        benchNum (1::(OddWord Word32 (Lit 20)))
    ]
