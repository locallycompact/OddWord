{-# LANGUAGE Haskell2010, ScopedTypeVariables, DataKinds, KindSignatures #-}

module Equiv where

import Prelude hiding (catch)
import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Gen
import Data.Bits
import Data.Maybe
import Data.Proxy
import Data.Word
import Data.Word.Odd
import Control.Applicative
import Control.Exception
import System.IO.Unsafe
import GHC.TypeLits

-- | Represents a range of unary functions which can be applied to a word.
data UFunc (n::Nat)
    = Add   Integer | Mul   Integer | Sub   Integer | SubR  Integer
    | Div   Integer | Mod   Integer | Quot  Integer | Rem   Integer
    | DivR  Integer | ModR  Integer | QuotR Integer | RemR  Integer
    | Neg           | Abs           | Inv           | AddDigit
    | From  Integer | And   Integer | Or    Integer | Xor   Integer
    | TstB  Int     | ClrB  Int     | SetB  Int     | InvB  Int
    | FromB Int     | Shift Int     | Rot   Int     | PopCnt
    | CntLZ         | CntTZ
    | AdjEnum Int Integer
    deriving Show

instance KnownNat n => Arbitrary (UFunc n) where
    arbitrary = oneof
        [Add   <$> choose (0, upper)
        ,Mul   <$> choose (0, upper)
        ,Sub   <$> choose (0, upper)
        ,SubR  <$> choose (0, upper)
        ,Div   <$> choose (0, upper)
        ,Mod   <$> choose (0, upper)
        ,Quot  <$> choose (0, upper)
        ,Rem   <$> choose (0, upper)
        ,DivR  <$> choose (0, upper)
        ,ModR  <$> choose (0, upper)
        ,QuotR <$> choose (0, upper)
        ,RemR  <$> choose (0, upper)
        ,return Neg
        ,return Abs
        ,return Inv
        ,return AddDigit
        ,From  <$> arbitrary
        ,And   <$> choose (0, upper)
        ,Or    <$> choose (0, upper)
        ,Xor   <$> choose (0, upper)
        ,TstB  <$> choose (0, 2*width)
        ,ClrB  <$> choose (0, 2*width)
        ,SetB  <$> choose (0, 2*width)
        ,InvB  <$> choose (0, 2*width)
        ,FromB <$> choose (0, 2*width)
        ,Shift <$> choose (0, 2*width)
        ,Rot   <$> choose (0, 2*width)
        ,return PopCnt
        ,return CntLZ
        ,return CntTZ
        ,AdjEnum <$> arbitrary <*> choose (0, upper)
        ]
        where width = fromIntegral $ natVal (Proxy :: Proxy n) 
              upper = shiftL 1 width - 1

-- | Total wrapper for 'div'.
safeDiv :: (Integral a, Bounded a) => a -> a -> a
safeDiv d 0 = maxBound
safeDiv d n = div d n

-- | Total wrapper for 'mod'.
safeMod :: (Integral a) => a -> a -> a
safeMod d 0 = 0
safeMod d n = mod d n

-- | Total wrapper for 'quot'.
safeQuot :: (Integral a, Bounded a) => a -> a -> a
safeQuot d 0 = maxBound
safeQuot d n = quot d n

-- | Total wrapper for 'rem'.
safeRem :: (Integral a) => a -> a -> a
safeRem d 0 = 0
safeRem d n = rem d n

-- | Total wrapper for 'toEnum'.
safeToEnum :: (Enum a) => a -> Int -> a
safeToEnum def x =
    unsafePerformIO (evaluate (toEnum x) `catch` \(ErrorCall _) -> return def)

-- | Interpreter for executing 'UFunc' values.
fromUFunc :: (Integral a, Bounded a, Enum a, FiniteBits a, Read a, Show a) =>
    UFunc n -> a -> a
fromUFunc (Add   i) x = x + (fromInteger i)
fromUFunc (Mul   i) x = x * (fromInteger i)
fromUFunc (Sub   i) x = x - (fromInteger i)
fromUFunc (SubR  i) x = (fromInteger i) - x
fromUFunc (Div   i) x = safeDiv  x (fromInteger i)
fromUFunc (Mod   i) x = safeMod  x (fromInteger i)
fromUFunc (Quot  i) x = safeQuot x (fromInteger i)
fromUFunc (Rem   i) x = safeRem  x (fromInteger i)
fromUFunc (DivR  i) x = safeDiv  (fromInteger i) x
fromUFunc (ModR  i) x = safeMod  (fromInteger i) x
fromUFunc (QuotR i) x = safeQuot (fromInteger i) x
fromUFunc (RemR  i) x = safeRem  (fromInteger i) x
fromUFunc  Neg      x = negate x
fromUFunc  Abs      x = abs x
fromUFunc  Inv      x = complement x
fromUFunc (From i)  _ = fromInteger i
fromUFunc  AddDigit x = read . ('1':) $ show x
fromUFunc (And   i) x = x .&. (fromInteger i)
fromUFunc (Or    i) x = x .|. (fromInteger i)
fromUFunc (Xor   i) x = xor x (fromInteger i)
fromUFunc (TstB  n) x = fromIntegral $ fromEnum $ testBit x n
fromUFunc (ClrB  n) x = clearBit x n
fromUFunc (SetB  n) x = setBit x n
fromUFunc (InvB  n) x = complementBit x n
fromUFunc (FromB n) _ = bit n
fromUFunc (Shift n) x = shift x n
fromUFunc (Rot   n) x = rotate x n
fromUFunc  PopCnt   x = fromIntegral $ popCount x
fromUFunc  CntLZ    x = fromIntegral $ countLeadingZeros x
fromUFunc  CntTZ    x = fromIntegral $ countTrailingZeros x
fromUFunc (AdjEnum i def) x = safeToEnum (fromIntegral def) . (+i) $ fromEnum x

-- | Checks that computations using real and simulated words produce the same
-- result for a series of 'UFunc's.
verifyEquivalence :: forall n a b.
    (KnownNat n,
     Integral a, Bounded a, Enum a, FiniteBits a, Read a, Show a,
     Integral b, Bounded b, Enum b, FiniteBits b, Read b, Show b) =>
    Proxy n -> Proxy a -> Proxy b -> Property
verifyEquivalence width _ _ = property $ \(us :: [UFunc n]) ->
    let refFn = foldr (.) id $ map fromUFunc us :: a -> a
        tstFn = foldr (.) id $ map fromUFunc us :: b -> b
    in toInteger (refFn 0) == toInteger (tstFn 0)

-- | A 16-bit word backed by something else.
type TestWord16 a = OddWord a (One (Zero (Zero (Zero (Zero ())))))
