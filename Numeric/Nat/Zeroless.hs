{-# LANGUAGE TypeFamilies, Rank2Types, TypeOperators, GADTs, EmptyDataDecls, FlexibleInstances, FlexibleContexts, UndecidableInstances  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Numeric.Nat.Zeroless
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- Zeroless numbers encoded in zeroless binary numbers
----------------------------------------------------------------------

module Numeric.Nat.Zeroless
  ( D0, D1, D2, (:+:), (:*:), Zeroless(..), fromNat
  , N8, N16, N32, N64
  , Fin(..)
  ) where

import Control.Applicative
import Data.Distributive
import Data.Functor.Representable
import Data.Functor.Bind
import Data.Foldable
import Data.Function (on)
import Data.Monoid
import Data.Traversable
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Key
import Prelude hiding (lookup)

infixl 7 :*:
infixl 6 :+: 

-- * Type-level naturals using zeroless binary numbers

data D0    -- ^ 0 
data D1 n  -- ^ 2n + 1
data D2 n  -- ^ 2n + 2

-- * useful numbers
type N1 = D1 D0
type N8  = D2 (D1 (D1 D0))
type N16 = D2 (D1 (D1 (D1 D0)))
type N32 = D2 (D1 (D1 (D1 (D1 D0))))
type N64 = D2 (D1 (D1 (D1 (D1 (D1 D0)))))

-- * Successor 
type family Succ n
type instance Succ D0 = D1 D0
type instance Succ (D1 n) = D2 n
type instance Succ (D2 n) = D1 (Succ n)

-- * Carry flags
data C0
data C1
data C2

-- * Add with carry
type family Add c n m
type instance Add C0 D0 n = n
type instance Add C1 D0 D0 = D1 D0
type instance Add C2 D0 D0 = D2 D0
type instance Add C1 D0 (D1 n) = D2 n
type instance Add C1 D0 (D2 n) = D1 (Add C1 D0 n) 
type instance Add C2 D0 (D1 n) = D1 (Add C1 D0 n)
type instance Add C2 D0 (D2 n) = D2 (Add C1 D0 n)
type instance Add C0 (D1 n) D0 = D1 n
type instance Add C1 (D1 n) D0 = D2 n
type instance Add C2 (D1 n) D0 = D1 (Add C1 D0 n)
type instance Add C0 (D1 n) (D1 m) = D2 (Add C0 n m)
type instance Add C1 (D1 n) (D1 m) = D1 (Add C1 n m)
type instance Add C2 (D1 n) (D1 m) = D2 (Add C1 n m)
type instance Add C0 (D1 n) (D2 m) = D1 (Add C1 n m)
type instance Add C1 (D1 n) (D2 m) = D2 (Add C1 n m)
type instance Add C2 (D1 n) (D2 m) = D1 (Add C2 n m)
type instance Add C0 (D2 n) D0 = D2 n
type instance Add C1 (D2 n) D0 = D1 (Add C1 D0 n)
type instance Add C2 (D2 n) D0 = D2 (Add C1 D0 n)
type instance Add C0 (D2 n) (D1 m) = D1 (Add C1 n m)
type instance Add C1 (D2 n) (D1 m) = D2 (Add C1 n m)
type instance Add C2 (D2 n) (D1 m) = D1 (Add C2 n m)
type instance Add C0 (D2 n) (D2 m) = D2 (Add C1 n m)
type instance Add C1 (D2 n) (D2 m) = D1 (Add C2 n m)
type instance Add C2 (D2 n) (D2 m) = D2 (Add C2 n m)

-- * Adder
type n :+: m = Add C0 n m

-- * Multiplier
type family n :*: m
type instance D0 :*: m = D0
type instance D1 n :*: m = (n :*: m) :+: (n :*: m) :+: m
type instance D2 n :*: m = (n :*: m) :+: (n :*: m) :+: m :+: m

-- * Digit Counter
type family Digits n
type instance Digits Zero = Zero
type instance Digits (D1 n) = Succ (Digits n)
type instance Digits (D2 n) = Succ (Digits n)

type family Reverse' n m
type instance Reverse' m D0     = m 
type instance Reverse' m (D1 n) = Reverse' (D1 m) n 
type instance Reverse' m (D2 n) = Reverse' (D2 m) n

-- * bitwise reversal
type Reverse n = Reverse' D0 n

-- * Class of zeroless-binary numbers
class Zeroless n where
  ind :: f D0 
      -> (forall m. Zeroless m => f m -> f (D1 m)) 
      -> (forall m. Zeroless m => f m -> f (D2 m))
      -> f n

instance Zeroless D0 where
  ind z _ _ = z 

instance Zeroless n => Zeroless (D1 n) where
  ind z f g = f (ind z f g)

instance Zeroless n => Zeroless (D2 n) where
  ind z f g = g (ind z f g)

class Zeroless n => Positive n
instance Zeroless n => Positive (D1 n)
instance Zeroless n => Positive (D2 n)

newtype Nat n = Nat { fromNat :: Int }

instance Zeroless n => Eq (Nat n) where
  _ == _ = True

instance Zeroless n => Ord (Nat n) where
  compare _ _ = EQ

instance Zeroless n => Show (Nat n) where
  showsPrec d (Nat n) = showsPrec d n

instance Zeroless n => Bounded (Nat n) where
  minBound = nat
  maxBound = nat

instance Zeroless n => Enum (Nat n) where
  fromEnum (Nat n) = n
  toEnum _ = nat

nat :: Zeroless n => Nat n 
nat = ind (Nat 0) 
          (Nat . (+1) . (*2) . fromNat) 
          (Nat . (+2) . (*2) . fromNat)

-- * A finite number @m < n@
newtype Fin n = Fin { fromFin :: Int } 

instance Show (Fin n) where
  showsPrec d = showsPrec d . fromFin

instance Eq (Fin n) where
  (==) = (==) `on` fromFin

instance Ord (Fin n) where
  compare = compare `on` fromFin 

instance Positive n => Num (Fin n) where
  fromInteger = toEnum . fromInteger
  a + b = toEnum (fromFin a + fromFin b)
  a * b = toEnum (fromFin a * fromFin b)
  a - b = toEnum (fromFin a - fromFin b)
  abs a = a
  signum 0 = 0
  signum _ = 1

inFin :: (Int -> Int) -> Fin n -> Fin n
inFin f = Fin . f . fromFin

instance Positive n => Bounded (Fin n) where
  minBound = Fin 0
  maxBound = inFin (subtract 1) $ 
             ind (Fin 0) 
                 (Fin . ((+1) . (*2)) . fromFin)
                 (Fin . ((+2) . (*2)) . fromFin)

instance Positive n => Enum (Fin n) where
  fromEnum = fromFin
  toEnum n = r where
    r | n < 0 = error "Fin.toEnum: negative number"
      | Fin n <= b = Fin n `asTypeOf` b
      | otherwise = error "Fin.toEnum: index out of range"
    b = maxBound
