{-# LANGUAGE Haskell2010, ScopedTypeVariables, DataKinds #-}

module Main where

import Data.Bits
import Data.Maybe
import Data.Word
import Data.Word.Odd
import Data.Proxy
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Equiv
import Props

-- | List of bit lengths for all words up to 63-bits.
preDefWordLengths :: [Int]
preDefWordLengths = [
    bits (0 :: Word1), bits (0 :: Word2), bits (0 :: Word3),
    bits (0 :: Word4), bits (0 :: Word5), bits (0 :: Word6),
    bits (0 :: Word7), bits (0 :: Word8), bits (0 :: Word9),
    bits (0 :: Word10), bits (0 :: Word11), bits (0 :: Word12),
    bits (0 :: Word13), bits (0 :: Word14), bits (0 :: Word15),
    bits (0 :: Word16), bits (0 :: Word17), bits (0 :: Word18),
    bits (0 :: Word19), bits (0 :: Word20), bits (0 :: Word21),
    bits (0 :: Word22), bits (0 :: Word23), bits (0 :: Word24),
    bits (0 :: Word25), bits (0 :: Word26), bits (0 :: Word27),
    bits (0 :: Word28), bits (0 :: Word29), bits (0 :: Word30),
    bits (0 :: Word31), bits (0 :: Word32), bits (0 :: Word33),
    bits (0 :: Word34), bits (0 :: Word35), bits (0 :: Word36),
    bits (0 :: Word37), bits (0 :: Word38), bits (0 :: Word39),
    bits (0 :: Word40), bits (0 :: Word41), bits (0 :: Word42),
    bits (0 :: Word43), bits (0 :: Word44), bits (0 :: Word45),
    bits (0 :: Word46), bits (0 :: Word47), bits (0 :: Word48),
    bits (0 :: Word49), bits (0 :: Word50), bits (0 :: Word51),
    bits (0 :: Word52), bits (0 :: Word53), bits (0 :: Word54),
    bits (0 :: Word55), bits (0 :: Word56), bits (0 :: Word57),
    bits (0 :: Word58), bits (0 :: Word59), bits (0 :: Word60),
    bits (0 :: Word61), bits (0 :: Word62), bits (0 :: Word63)]
    where bits n = finiteBitSize n

typeLitWordLengths :: [Int]
typeLitWordLengths = [
    finiteBitSize (0 :: OddWord Word8 (Lit 1)),
    finiteBitSize (0 :: OddWord Word8 (Lit 2)),
    finiteBitSize (0 :: OddWord Word8 (Lit 3)),
    finiteBitSize (0 :: OddWord Word8 (Lit 4))]

checkWordLengths :: [Int] -> Expectation
checkWordLengths =
    flip shouldBe [] .
    map fst . filter snd . map (\t -> (t,uncurry (/=) t)) .  zip [1..]

main :: IO ()
main = hspec $ do
    describe "Predefined odd word synonyms" $
        it "have the correct length" $
            checkWordLengths preDefWordLengths
    describe "Odd words with type literals" $
        it "have the correct length" $
            checkWordLengths typeLitWordLengths
    modifyMaxSuccess (const 5000) $ describe "Word16" $ do
        it "is equivalent to TestWord16 Word16" $
            verifyEquivalence (Proxy :: Proxy 16)
                (Proxy :: Proxy Word16) (Proxy :: Proxy (TestWord16 Word16))
        it "is equivalent to TestWord16 Word32" $
            verifyEquivalence (Proxy :: Proxy 16)
                (Proxy :: Proxy Word16) (Proxy :: Proxy (TestWord16 Word32))
        it "is equivalent to TestWord16 Word64" $
            verifyEquivalence (Proxy :: Proxy 16)
                (Proxy :: Proxy Word16) (Proxy :: Proxy (TestWord16 Word64))
        it "is equivalent to TestWord16 Integer" $
            verifyEquivalence (Proxy :: Proxy 16)
                (Proxy :: Proxy Word16) (Proxy :: Proxy (TestWord16 Integer))
    describe "Word20" $ do
        it "is in bounds" $ 
            propInBounds (Proxy :: Proxy 20) (Proxy :: Proxy Word20)
        it "can rotate left and right" $ 
            propRotateRL (Proxy :: Proxy Word20)
    describe "Word2000" $ do
        it "is in bounds" $ 
            propInBounds (Proxy :: Proxy 2000)
                         (Proxy :: Proxy (OddWord Integer (Lit 2000)))
        it "can rotate left and right" $ 
            propRotateRL (Proxy :: Proxy (OddWord Integer (Lit 2000)))
