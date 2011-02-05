{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable.Trie
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Data.Functor.Representable.Trie
  ( 
  -- * Representations of polynomial functors
    HasTrie(..)
  -- * Memoizing functions
  , mup, memo, memo2, memo3
  , inTrie, inTrie2, inTrie3
  -- * Workarounds for current GHC limitations
  , trie, untrie
  , coerceKey, uncoerceKey
  ) where

import Control.Monad.Representable
import Data.Eq.Type
import Data.Functor.Identity
import Data.Functor.Product
import Data.Key
import Prelude hiding (lookup)

-- class (TraversableWithKey1 (Trie a), Representable (Trie a), Key (Trie a) ~ a) => HasTrie a where
class (TraversableWithKey1 (Trie a), Representable (Trie a)) => HasTrie a where
  type Trie a :: * -> *
  -- | Ideally we would have the constraint @Key (Trie a) ~ a@ as a class constraint. 
  -- We are forced to approximate this using an explicit equality witness until GHC implements this feature.
  keyRefl :: a := Key (Trie a)

coerceKey :: HasTrie a => a -> Key (Trie a)
coerceKey = go keyRefl where
  go :: HasTrie a => (a := Key (Trie a)) -> a -> Key (Trie a)
  go Refl = id

uncoerceKey :: HasTrie a => Key (Trie a) -> a
uncoerceKey = go keyRefl where
  go :: HasTrie a => (a := Key (Trie a)) -> Key (Trie a) -> a
  go Refl = id

-- Matt Hellige's notation for @argument f . result g@.
-- <http://matt.immute.net/content/pointless-fun>
(~>) :: (a' -> a) -> (b -> b') -> (a -> b) -> a' -> b'
g ~> f = (f .) . (. g)

untrie :: HasTrie t => Trie t a -> t -> a
untrie = go keyRefl where
  go :: HasTrie t => (t := Key (Trie t)) -> Trie t a -> t -> a
  go Refl = index

trie :: HasTrie t => (t -> a) -> Trie t a
trie = go keyRefl where
  go :: HasTrie t => (t := Key (Trie t)) -> (t -> a) -> Trie t a
  go Refl = tabulate

{-# RULES
"trie/untrie" forall t. trie (untrie t) = t
 #-}

memo :: HasTrie t => (t -> a) -> t -> a
memo = untrie . trie

-- | Lift a memoizer to work with one more argument.
mup :: HasTrie t => (b -> c) -> (t -> b) -> t -> c
mup mem f = memo (mem . f)

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (HasTrie s, HasTrie t) => (s -> t -> a) -> s -> t -> a
memo2 = mup memo

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (HasTrie r, HasTrie s, HasTrie t) => (r -> s -> t -> a) -> r -> s -> t -> a
memo3 = mup memo2

-- | Apply a unary function inside of a tabulate
inTrie 
  :: (HasTrie a, HasTrie c) 
  => ((a -> b) -> c -> d)
  -> Trie a b -> Trie c d
inTrie = untrie ~> trie

-- | Apply a binary function inside of a tabulate
inTrie2 
  :: (HasTrie a, HasTrie c, HasTrie e) 
  => ((a -> b) -> (c -> d) -> e -> f)
  -> Trie a b -> Trie c d -> Trie e f
inTrie2 = untrie ~> inTrie

-- | Apply a ternary function inside of a tabulate
inTrie3 
  :: (HasTrie a, HasTrie c, HasTrie e, HasTrie g) 
  => ((a -> b) -> (c -> d) -> (e -> f) -> g -> h)
  -> Trie a b -> Trie c d -> Trie e f -> Trie g h
inTrie3 = untrie ~> inTrie2

-- * Instances

instance HasTrie () where
  type Trie () = Identity
  keyRefl = Refl

instance (HasTrie a, HasTrie b) => HasTrie (a, b) where
  type Trie (a, b) = RepT (Trie a) (Trie b)
  keyRefl = go keyRefl keyRefl where
    go :: (a := Key (Trie a)) -> (b := Key (Trie b)) -> (a, b) := Key (Trie (a,b))
    go Refl Refl = Refl

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type Trie (Either a b) = Product (Trie a) (Trie b)
  keyRefl = go keyRefl keyRefl where
    go :: (a := Key (Trie a)) -> (b := Key (Trie b)) -> Either a b := Key (Trie (Either a b))
    go Refl Refl = Refl
