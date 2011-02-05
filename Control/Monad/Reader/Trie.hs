{-# LANGUAGE TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Reader.Trie
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Control.Monad.Reader.Trie ( 
  -- * A "Representable Trie"-based Reader monad transformer
    ReaderTrieT(..)
  , module Data.Functor.Representable.Trie
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
import Data.Functor.Representable.Trie
import Data.Foldable
import Data.Key
import Data.Monoid
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (lookup)

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

instance (HasTrie a, Indexable m) => Indexable (ReaderTrieT a m) where
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

