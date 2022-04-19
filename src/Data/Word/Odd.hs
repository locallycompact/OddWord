{-# LANGUAGE Haskell2010, ScopedTypeVariables, CPP,
             DeriveDataTypeable, DataKinds, KindSignatures,
             TypeFamilies, TypeOperators, UndecidableInstances, FlexibleContexts #-}

module Data.Word.Odd (
    -- * Odd Word Wrapper
    OddWord,

    -- * Type Numbers
    TypeNum,
    One,
    Zero,
    Lit,

    -- * Finite Bits
    FiniteBitsBase(
        subWordClz,
        subWordCtz),

    -- * Predefined Odd Words
    Word1, Word2, Word3, Word4, Word5, Word6, Word7,
    Word9,  Word10, Word11, Word12, Word13, Word14, Word15,
    Word17, Word18, Word19, Word20, Word21, Word22, Word23, Word24,
    Word25, Word26, Word27, Word28, Word29, Word30, Word31,
    Word33, Word34, Word35, Word36, Word37, Word38, Word39, Word40,
    Word41, Word42, Word43, Word44, Word45, Word46, Word47, Word48,
    Word49, Word50, Word51, Word52, Word53, Word54, Word55, Word56,
    Word57, Word58, Word59, Word60, Word61, Word62, Word63
) where

import Data.Bits
import Data.Proxy
import Data.Word
import Data.Function
import Data.Typeable
import GHC.TypeLits

-- | 'OddWord' provides a range of unsigned integer word types with a length in
-- bits encoded at the type level. The first type parameter @a@ must supply an
-- integer type which can hold at least as many bits as required for the
-- 'OddWord'. The second type paramter @n@ then encodes the length in bits
-- which the 'OddWord' will be restricted to.
--
-- The length of the 'OddWord' can be encoded as a string of binary digits
-- using the 'One', 'Zero', and @()@ type constructors. The outermost
-- constructor specifies the most significant digit and each subsequent digit
-- is nested inside the previous type constructor via its type parameter. Hence,
-- the encoding is terminated by the @()@ type constructor. For example, the
-- number 4 would be expressed as: @One (Zero (Zero ()))@.
--
-- Alternatively, if the compiler supports type-level naturals then these can
-- be used via the 'Lit' type constructor. For example, the number 4 can be
-- expressed as: @Lit 4@.
--
-- To supply a complete example, a 4-bit integer type could be built from a
-- 'Word8' and specified as either @OddWord Word8 (One (Zero (Zero ())))@ or
-- @OddWord Word8 (Lit 4)@.
--
-- The behaviour of an 'OddWord' is undefined if the specified length is
-- greater than that of the underlying integer type. The behaviour is also
-- undefined if the specified length is equal to that of the underlying integer
-- type and that type is also signed.
newtype OddWord a n = OW {unOW :: a} deriving (Eq, Ord, Typeable)

data TypeNumBuilder a = TypeNumBuilder Int Int

fromTypeNum :: TypeNumBuilder a -> Int
fromTypeNum (TypeNumBuilder x _) = x

-- | Intances of 'TypeNum' represent type-level numbers.
class TypeNum a where
    typeNum :: TypeNumBuilder a

-- | Represents a type-level number with a leading one bit followed by the
-- string of digits specified by @a@.
data One a deriving Typeable

-- | Represents a type-level number with a placeholder zero bit followed by the
-- string of digits specified by @a@.
data Zero a deriving Typeable

-- | Converts a native GHC type-level natural into one usable by this library.
-- This requires the @DataKinds@ extension.
data Lit :: Nat -> * deriving Typeable

instance TypeNum () where
    typeNum = TypeNumBuilder 0 0

instance (TypeNum a) => TypeNum (One a) where
    typeNum = let (TypeNumBuilder n m) = (typeNum :: TypeNumBuilder a)
              in TypeNumBuilder (n+bit m) (m+1)

instance (TypeNum a) => TypeNum (Zero a) where
    typeNum = let (TypeNumBuilder n m) = (typeNum :: TypeNumBuilder a)
              in TypeNumBuilder (n) (m+1)

-- | Provides a more efficient mechanism for converting 'Nat'-kinded types into
-- small integers than 'KnownNat'.
#if MIN_VERSION_base(4,11,0)
-- Decomposes Nats in log2(n) recursions, one bit at a time.
data ZNat = IsZ | NonZE Nat | NonZO Nat

type family ToZNatImpl (n::Nat) (lsb::Nat) where
    ToZNatImpl 0 0 = IsZ
    ToZNatImpl n 0 = NonZE n
    ToZNatImpl n 1 = NonZO n

type ToZNat n = ToZNatImpl n (Mod n 2)

class ZNatValue (n::ZNat) where
    znatIntVal :: proxy n -> Int

instance ZNatValue IsZ where
    znatIntVal _ = 0
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (Div n 2)) => ZNatValue (NonZE n) where
    znatIntVal _ = 2 * (znatIntVal (Proxy :: Proxy (ToZNat (Div n 2))))
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (Div n 2)) => ZNatValue (NonZO n) where
    znatIntVal _ = 1 + 2 * (znatIntVal (Proxy :: Proxy (ToZNat (Div n 2))))
    {-# INLINE znatIntVal #-}
#else
-- For older GHCs that don't support Div and Mod, decomposes Nats in
-- 16*log16(n) recursions for values of n below 2^16.
data ZNat = IsZ | NonZ Nat | NonZ4 Nat | NonZ8 Nat | NonZ12 Nat

-- Regarding u, v, and w, GHC 7.10 doesn't like wildcards in type families.
type family ToZNatImpl
        (n::Nat) (nz4::Ordering) (nz8::Ordering) (nz12::Ordering) where
    ToZNatImpl 0 LT LT LT = IsZ
    ToZNatImpl n LT LT LT = NonZ n
    ToZNatImpl n u  LT LT = NonZ4 n
    ToZNatImpl n u  v  LT = NonZ8 n
    ToZNatImpl n u  v  w  = NonZ12 n

type ToZNat n = ToZNatImpl n (CmpNat n 16) (CmpNat n 256) (CmpNat n 4096)

class ZNatValue (n::ZNat) where
    znatIntVal :: proxy n -> Int

instance ZNatValue IsZ where
    znatIntVal _ = 0
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (n - 1)) => ZNatValue (NonZ n) where
    znatIntVal _ = 1 + (znatIntVal (Proxy :: Proxy (ToZNat (n - 1))))
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (n - 16)) => ZNatValue (NonZ4 n) where
    znatIntVal _ = 16 + (znatIntVal (Proxy :: Proxy (ToZNat (n - 16))))
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (n - 256)) => ZNatValue (NonZ8 n) where
    znatIntVal _ = 256 + (znatIntVal (Proxy :: Proxy (ToZNat (n - 256))))
    {-# INLINE znatIntVal #-}

instance ZNatValue (ToZNat (n - 4096)) => ZNatValue (NonZ12 n) where
    znatIntVal _ = 4096 + (znatIntVal (Proxy :: Proxy (ToZNat (n - 4096))))
    {-# INLINE znatIntVal #-}
#endif

instance (ZNatValue (ToZNat n)) => TypeNum (Lit n) where
    typeNum = TypeNumBuilder
        (fromIntegral $ znatIntVal (Proxy :: Proxy (ToZNat n))) 0

-- | Required to implement 'FiniteBits' for an 'OddWord' based on type @a@.
class Bits a => FiniteBitsBase a where
    -- | Count the leading zeros on a @w@-bit wide word.
    subWordClz :: Int -> a -> Int
    subWordClz w x = (w-1) - worker (w-1)
        where worker i | i < 0       = i
                       | testBit x i = i
                       | otherwise   = worker (i-1)
    -- | Count the trailing zeros on a @w@-bit wide word.
    subWordCtz :: Int -> a -> Int
    subWordCtz w x = worker 0
        where worker i | i >= w      = i
                       | testBit x i = i
                       | otherwise   = worker (i+1)

instance FiniteBitsBase Word8 where
    subWordClz w x = countLeadingZeros x + w - finiteBitSize x
    subWordCtz w x = min (countTrailingZeros x) w

instance FiniteBitsBase Word16 where
    subWordClz w x = countLeadingZeros x + w - finiteBitSize x
    subWordCtz w x = min (countTrailingZeros x) w

instance FiniteBitsBase Word32 where
    subWordClz w x = countLeadingZeros x + w - finiteBitSize x
    subWordCtz w x = min (countTrailingZeros x) w

instance FiniteBitsBase Word64 where
    subWordClz w x = countLeadingZeros x + w - finiteBitSize x
    subWordCtz w x = min (countTrailingZeros x) w

instance FiniteBitsBase Integer where

-- | Wraps both parts of a homogenous pair with the OddWord constructor.
pairOW :: (a, a) -> (OddWord a n, OddWord a n)
pairOW = uncurry ((,) `on` OW)

-- | An OddWord with all the bits set, used for masking.
owMask :: forall a n. (Num a, Bits a, TypeNum n) => OddWord a n
owMask = OW . (flip (-) 1) . bit $ fromTypeNum (typeNum :: TypeNumBuilder n)

-- | Smart constructor for OddWords which masks off the unused upper bits.
maskOW :: forall a n. (Num a, Bits a, TypeNum n) => a -> OddWord a n
maskOW w = OW $ w .&. unOW (owMask :: OddWord a n)

-- | Applies a function to the first component of each pair in a list thereof.
mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f xs = map (\(a,c) -> (f a,c)) xs

--
-- Instances for the OddWord type
--
-- The instances largely forward operations to the underlying integer type
-- while wrapping and unwrapping the newtype, and masking or otherwise
-- adjusting the results as appropriate for the desired bit length of the word.
--

instance (Show a) => Show (OddWord a n) where
    showsPrec p (OW x) s = showsPrec p x s
    show (OW x)          = show x
    showList xs          = showList $ map unOW xs 

instance (Read a, Num a, Bits a, TypeNum n) => Read (OddWord a n) where
    readsPrec p s = mapFst maskOW $ readsPrec p s
    readList s    = mapFst (map maskOW) $ readList s

instance (Num a, Bits a, TypeNum n) => Num (OddWord a n) where
    (OW l) + (OW r) = maskOW $ (l + r)
    (OW l) * (OW r) = maskOW $ (l * r)
    (OW l) - (OW r) = maskOW $ (l - r)
    negate (OW x)   = maskOW $ negate x
    abs w = w
    signum (OW x) | x == 0    = 0
                  | otherwise = 1
    fromInteger i = maskOW $ fromInteger i 

instance (Real a, Bits a, TypeNum n) => Real (OddWord a n) where
    toRational (OW x) = toRational x

instance (Num a, Bits a, TypeNum n) => Bounded (OddWord a n) where
    minBound = 0
    maxBound = owMask

instance (Enum a, Ord a, Num a, Bits a, TypeNum n) => Enum (OddWord a n) where
    succ x = x + 1
    pred x = x - 1
    toEnum i | i >= 0 && fromIntegral i <= unOW (owMask :: OddWord a n)
             = OW $ toEnum i
             | otherwise = error "OddWord: toEnum: Index out of bounds."
    fromEnum (OW x) = fromEnum x
    enumFrom x = enumFromTo x owMask
    enumFromThen x1 x2 = enumFromThenTo x1 x2 bound
                         where bound | x2 >= x1 = owMask
                                     | otherwise = 0
    enumFromTo (OW x) (OW y) = map OW $ enumFromTo x y
    enumFromThenTo (OW x1) (OW x2) (OW y) = map OW $ enumFromThenTo x1 x2 y

instance (Integral a, Bits a, TypeNum n) => Integral (OddWord a n) where
    quot (OW n) (OW d) = OW $ quot n d
    rem  (OW n) (OW d) = OW $ rem n d
    div  (OW n) (OW d) = OW $ div n d
    mod  (OW n) (OW d) = OW $ mod n d
    quotRem (OW n) (OW d) = pairOW $ quotRem n d
    divMod  (OW n) (OW d) = pairOW $ divMod n d
    toInteger (OW x) = toInteger x

instance (Num a, Bits a, TypeNum n) => Bits (OddWord a n) where
    (OW l) .&. (OW r) = OW $ l .&. r
    (OW l) .|. (OW r) = OW $ l .|. r
    xor (OW l) (OW r) = OW $ xor l r
    complement x = x `xor` owMask
    bit n | n < fromTypeNum (typeNum :: TypeNumBuilder n)
          = OW $ bit n
          | otherwise = OW 0
    setBit (OW x) n | n < fromTypeNum (typeNum :: TypeNumBuilder n)
                    = OW $ setBit x n
                    | otherwise = OW x
    clearBit (OW x) n = OW $ clearBit x n
    complementBit (OW x) n | n < fromTypeNum (typeNum :: TypeNumBuilder n)
                           = OW $ complementBit x n
                           | otherwise = OW x
    testBit (OW x) n = testBit x n
    bitSize _ = fromTypeNum (typeNum :: TypeNumBuilder n)
    bitSizeMaybe _ = Just $ fromTypeNum (typeNum :: TypeNumBuilder n)
    isSigned _ = False 
    shiftL (OW x) n = maskOW $ shiftL x n
    shiftR (OW x) n = OW $ shiftR x n
    rotateL (OW x) n = OW $
        (shiftL x n' .&. unOW (owMask :: OddWord a n)) .|. shiftR x (w-n')
        where n' = n `mod` w
              w = fromTypeNum (typeNum :: TypeNumBuilder n)
    rotateR (OW x) n = OW $
        shiftR x n' .|. (shiftL x (w-n') .&. unOW (owMask :: OddWord a n))
        where n' = n `mod` w
              w  = fromTypeNum (typeNum :: TypeNumBuilder n)
    popCount (OW x) = popCount x

instance (Num a, FiniteBitsBase a, TypeNum n) => FiniteBits (OddWord a n) where
    finiteBitSize _ = fromTypeNum (typeNum :: TypeNumBuilder n) 
    countLeadingZeros (OW x) =
        subWordClz (fromTypeNum (typeNum :: TypeNumBuilder n)) x
    countTrailingZeros (OW x) =
        subWordCtz (fromTypeNum (typeNum :: TypeNumBuilder n)) x

--
-- Predefined Odd Words
--

type Word1  = OddWord Word8             (One  ())
type Word2  = OddWord Word8        (One (Zero ()))
type Word3  = OddWord Word8        (One (One  ()))
type Word4  = OddWord Word8  (One (Zero (Zero ())))
type Word5  = OddWord Word8  (One (Zero (One  ())))
type Word6  = OddWord Word8  (One (One  (Zero ())))
type Word7  = OddWord Word8  (One (One  (One  ())))
--type Word8
type Word9  = OddWord Word16 (One (Zero (Zero (One  ()))))
type Word10 = OddWord Word16 (One (Zero (One  (Zero ()))))
type Word11 = OddWord Word16 (One (Zero (One  (One  ()))))
type Word12 = OddWord Word16 (One (One  (Zero (Zero ()))))
type Word13 = OddWord Word16 (One (One  (Zero (One  ()))))
type Word14 = OddWord Word16 (One (One  (One  (Zero ()))))
type Word15 = OddWord Word16 (One (One  (One  (One  ()))))
--type Word16
type Word17 = OddWord Word32 (One (Zero (Zero (Zero (One  ())))))
type Word18 = OddWord Word32 (One (Zero (Zero (One  (Zero ())))))
type Word19 = OddWord Word32 (One (Zero (Zero (One  (One  ())))))
type Word20 = OddWord Word32 (One (Zero (One  (Zero (Zero ())))))
type Word21 = OddWord Word32 (One (Zero (One  (Zero (One  ())))))
type Word22 = OddWord Word32 (One (Zero (One  (One  (Zero ())))))
type Word23 = OddWord Word32 (One (Zero (One  (One  (One  ())))))
type Word24 = OddWord Word32 (One (One  (Zero (Zero (Zero ())))))
type Word25 = OddWord Word32 (One (One  (Zero (Zero (One  ())))))
type Word26 = OddWord Word32 (One (One  (Zero (One  (Zero ())))))
type Word27 = OddWord Word32 (One (One  (Zero (One  (One  ())))))
type Word28 = OddWord Word32 (One (One  (One  (Zero (Zero ())))))
type Word29 = OddWord Word32 (One (One  (One  (Zero (One  ())))))
type Word30 = OddWord Word32 (One (One  (One  (One  (Zero ())))))
type Word31 = OddWord Word32 (One (One  (One  (One  (One  ())))))
--type Word32
type Word33 = OddWord Word64 (One (Zero (Zero (Zero (Zero (One  ()))))))
type Word34 = OddWord Word64 (One (Zero (Zero (Zero (One  (Zero ()))))))
type Word35 = OddWord Word64 (One (Zero (Zero (Zero (One  (One  ()))))))
type Word36 = OddWord Word64 (One (Zero (Zero (One  (Zero (Zero ()))))))
type Word37 = OddWord Word64 (One (Zero (Zero (One  (Zero (One  ()))))))
type Word38 = OddWord Word64 (One (Zero (Zero (One  (One  (Zero ()))))))
type Word39 = OddWord Word64 (One (Zero (Zero (One  (One  (One  ()))))))
type Word40 = OddWord Word64 (One (Zero (One  (Zero (Zero (Zero ()))))))
type Word41 = OddWord Word64 (One (Zero (One  (Zero (Zero (One  ()))))))
type Word42 = OddWord Word64 (One (Zero (One  (Zero (One  (Zero ()))))))
type Word43 = OddWord Word64 (One (Zero (One  (Zero (One  (One  ()))))))
type Word44 = OddWord Word64 (One (Zero (One  (One  (Zero (Zero ()))))))
type Word45 = OddWord Word64 (One (Zero (One  (One  (Zero (One  ()))))))
type Word46 = OddWord Word64 (One (Zero (One  (One  (One  (Zero ()))))))
type Word47 = OddWord Word64 (One (Zero (One  (One  (One  (One  ()))))))
type Word48 = OddWord Word64 (One (One  (Zero (Zero (Zero (Zero ()))))))
type Word49 = OddWord Word64 (One (One  (Zero (Zero (Zero (One  ()))))))
type Word50 = OddWord Word64 (One (One  (Zero (Zero (One  (Zero ()))))))
type Word51 = OddWord Word64 (One (One  (Zero (Zero (One  (One  ()))))))
type Word52 = OddWord Word64 (One (One  (Zero (One  (Zero (Zero ()))))))
type Word53 = OddWord Word64 (One (One  (Zero (One  (Zero (One  ()))))))
type Word54 = OddWord Word64 (One (One  (Zero (One  (One  (Zero ()))))))
type Word55 = OddWord Word64 (One (One  (Zero (One  (One  (One  ()))))))
type Word56 = OddWord Word64 (One (One  (One  (Zero (Zero (Zero ()))))))
type Word57 = OddWord Word64 (One (One  (One  (Zero (Zero (One  ()))))))
type Word58 = OddWord Word64 (One (One  (One  (Zero (One  (Zero ()))))))
type Word59 = OddWord Word64 (One (One  (One  (Zero (One  (One  ()))))))
type Word60 = OddWord Word64 (One (One  (One  (One  (Zero (Zero ()))))))
type Word61 = OddWord Word64 (One (One  (One  (One  (Zero (One  ()))))))
type Word62 = OddWord Word64 (One (One  (One  (One  (One  (Zero ()))))))
type Word63 = OddWord Word64 (One (One  (One  (One  (One  (One  ()))))))
