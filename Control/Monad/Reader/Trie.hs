{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Representable.Trie
-- Copyright   :  (c) Edward Kmett 2011
--                (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Control.Monad.Reader.Trie
  ( 
  -- * Representations of polynomial functors
    HasTrie(..)
  -- * A Trie-based Reader monad transformer
  , ReaderTrieT(..)
  -- * Memoizing functions
  , mup, memo, memo2, memo3
  , inTrie, inTrie2, inTrie3
  -- * Workarounds for current GHC limitations
  , (:=)(..)
  , trie, untrie
  , coerceKey, uncoerceKey
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Representable
import Control.Monad.Writer.Class as Writer
import Data.Distributive
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Foldable
import Data.Key
import Data.Monoid
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (lookup)

data a := b where Refl :: a := a

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

instance HasTrie () where
  type Trie () = Identity
  keyRefl = Refl

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

instance (HasTrie a, HasTrie b) => HasTrie (a,b) where
  type Trie (a,b) = RepT (Trie a) (Trie b)
  keyRefl = go keyRefl keyRefl where
    go :: (a := Key (Trie a)) -> (b := Key (Trie b)) -> (a, b) := Key (Trie (a,b))
    go Refl Refl = Refl

type instance Key (ReaderTrieT a m) = (a, Key m)

newtype ReaderTrieT a m b = ReaderTrieT { runReaderTrieT :: Trie a (m b) } 

instance (HasTrie a, Functor m) => Functor (ReaderTrieT a m) where
  fmap f = ReaderTrieT . fmap (fmap f) . runReaderTrieT

instance (HasTrie a, Apply m) => Apply (ReaderTrieT a m) where
  ReaderTrieT ff <.> ReaderTrieT fa = ReaderTrieT ((<.>) <$> ff <.> fa)

instance (HasTrie a, Applicative m) => Applicative (ReaderTrieT a m) where
  pure = ReaderTrieT . pure . pure 
  ReaderTrieT ff <*> ReaderTrieT fa = ReaderTrieT ((<*>) <$> ff <*> fa)

instance (HasTrie a, Bind m) => Bind (ReaderTrieT a m) where
  ReaderTrieT fm >>- f = ReaderTrieT $ tabulate (\a -> index fm a >>- flip index a . runReaderTrieT . f)

instance (HasTrie a, Monad m) => Monad (ReaderTrieT a m) where
  return = ReaderTrieT . pure . return
  ReaderTrieT fm >>= f = ReaderTrieT $ tabulate (\a -> index fm a >>= flip index a . runReaderTrieT . f)

instance (HasTrie a, Monad m) => MonadReader a (ReaderTrieT a m) where 
  ask = ReaderTrieT (trie return)
  local f (ReaderTrieT fm) = ReaderTrieT (tabulate (index fm . coerceKey . f . uncoerceKey))

instance HasTrie a => MonadTrans (ReaderTrieT a) where
  lift = ReaderTrieT . pure 

instance (HasTrie a, Distributive m) => Distributive (ReaderTrieT a m) where
  distribute = ReaderTrieT . fmap distribute . collect runReaderTrieT

instance (HasTrie a, Keyed m) => Keyed (ReaderTrieT a m) where
  mapWithKey f = ReaderTrieT . mapWithKey (\k -> mapWithKey (f . (,) (uncoerceKey k))) . runReaderTrieT

instance (HasTrie a, Index m) => Index (ReaderTrieT a m) where
  index = uncurry . fmap index . untrie . runReaderTrieT

instance (HasTrie a, Lookup (Trie a), Lookup m) => Lookup (ReaderTrieT a m) where
  lookup (k,k') (ReaderTrieT fm) = lookup (coerceKey k) fm >>= lookup k'

instance (HasTrie a, Representable m) => Representable (ReaderTrieT a m) where
  tabulate = ReaderTrieT . trie . fmap tabulate . curry
  
instance (HasTrie a, Foldable m) => Foldable (ReaderTrieT a m) where
  foldMap f = foldMap (foldMap f) . runReaderTrieT

instance (HasTrie a, Foldable1 m) => Foldable1 (ReaderTrieT a m) where
  foldMap1 f = foldMap1 (foldMap1 f) . runReaderTrieT

instance (HasTrie a, FoldableWithKey m) => FoldableWithKey (ReaderTrieT a m) where
  foldMapWithKey f = foldMapWithKey (\k -> foldMapWithKey (f . (,) (uncoerceKey k))) . runReaderTrieT

instance (HasTrie a, FoldableWithKey1 m) => FoldableWithKey1 (ReaderTrieT a m) where
  foldMapWithKey1 f = foldMapWithKey1 (\k -> foldMapWithKey1 (f . (,) (uncoerceKey k))) . runReaderTrieT 

instance (HasTrie a, Traversable m) => Traversable (ReaderTrieT a m) where
  traverse f = fmap ReaderTrieT . traverse (traverse f) . runReaderTrieT

instance (HasTrie a, Traversable1 m) => Traversable1 (ReaderTrieT a m) where
  traverse1 f = fmap ReaderTrieT . traverse1 (traverse1 f) . runReaderTrieT

instance (HasTrie a, TraversableWithKey m) => TraversableWithKey (ReaderTrieT a m) where
  traverseWithKey f = fmap ReaderTrieT . traverseWithKey (\k -> traverseWithKey (f . (,) (uncoerceKey k))) . runReaderTrieT

instance (HasTrie a, TraversableWithKey1 m) => TraversableWithKey1 (ReaderTrieT a m) where
  traverseWithKey1 f = fmap ReaderTrieT . traverseWithKey1 (\k -> traverseWithKey1 (f . (,) (uncoerceKey k))) . runReaderTrieT

instance (HasTrie a, Representable m, Semigroup a, Semigroup (Key m)) => Extend (ReaderTrieT a m) where
  extend = extendRep
  duplicate = duplicateRep

instance (HasTrie a, Representable m, Semigroup a, Semigroup (Key m), Monoid a, Monoid (Key m)) => Comonad (ReaderTrieT a m) where
  extract = extractRep

instance (HasTrie a, MonadIO m) => MonadIO (ReaderTrieT a m) where
  liftIO = lift . liftIO 

instance (HasTrie a, MonadWriter w m) => MonadWriter w (ReaderTrieT a m) where
  tell = lift . tell
  listen = ReaderTrieT . tabulate . fmap Writer.listen . index . runReaderTrieT
  pass = ReaderTrieT . tabulate . fmap Writer.pass . index . runReaderTrieT
