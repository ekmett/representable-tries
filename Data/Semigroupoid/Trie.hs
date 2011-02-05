{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Semigroupoid.Trie
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- We may not be able to build a category out of tries, but we can
-- consruct a semigroupoid.
----------------------------------------------------------------------

module Data.Semigroupoid.Trie
  ( (:->:)(..)
  , Entry(..)
  , runT
  ) where

import Control.Applicative
import Control.Arrow (first,(&&&))
import Control.Comonad
import Control.Monad.Representable
import Control.Monad.Reader
import Control.Monad.Reader.Trie
import Data.Bits
import Data.Distributive
import Data.Function (on)
import Data.Functor.Adjunction
import Data.Functor.Bind
import Data.Foldable
import Data.Int
import Data.Key
import Data.Monoid
import Data.Traversable
import Data.Semigroup
import Data.Semigroup.Traversable
import Data.Semigroup.Foldable
import Data.Semigroupoid
-- import Data.Semigroupoid.Ob
import Data.Word

data a :->: b where
  T :: HasTrie a => Trie a b -> a :->: b

type instance Key ((:->:) a) = a

data Entry a b = Entry a b

instance Functor (Entry a) where
  fmap f (Entry a b) = Entry a (f b)

runT :: (a :->: b) -> Trie a b
runT (T f) = f

instance Index ((:->:)e) where
  index (T f) = untrie f

instance HasTrie e => Distributive ((:->:)e) where
  distribute = distributeRep

instance HasTrie e => Representable ((:->:) e) where
  tabulate f = T (trie f)

instance HasTrie e => Adjunction (Entry e) ((:->:) e) where
  unit = mapWithKey Entry . pure
  counit (Entry a t) = index t a

instance Functor ((:->:) a) where
  fmap f (T g) = T (fmap f g)

instance Keyed ((:->:) a) where
  mapWithKey f (T a) = T (mapWithKey (f . uncoerceKey) a)

instance Foldable ((:->:) a) where
  foldMap f (T a) = foldMap f a

instance FoldableWithKey ((:->:) a) where
  foldMapWithKey f (T a) = foldMapWithKey (f . uncoerceKey) a

instance Traversable ((:->:) a) where
  traverse f (T a) = T <$> traverse f a

instance TraversableWithKey ((:->:) a) where
  traverseWithKey f (T a) = T <$> traverseWithKey (f . uncoerceKey) a

instance Foldable1 ((:->:) a) where
  foldMap1 f (T a) = foldMap1 f a

instance FoldableWithKey1 ((:->:) a) where
  foldMapWithKey1 f (T a) = foldMapWithKey1 (f . uncoerceKey) a

instance Traversable1 ((:->:) a) where
  traverse1 f (T a) = T <$> traverse1 f a

instance TraversableWithKey1 ((:->:) a) where
  traverseWithKey1 f (T a) = T <$> traverseWithKey1 (f . uncoerceKey) a

instance Eq b => Eq (a :->: b) where
  (==) = (==) `on` toList

instance Ord b => Ord (a :->: b) where
  compare = compare `on` toList

instance (Show a, Show b) => Show (a :->: b) where 
  showsPrec d t = showsPrec d (toIndexedList t)

instance Apply ((:->:) a) where
  T f <.> T g = T (f <.> g)
  a <. _ = a
  _ .> b = b

instance Semigroupoid (:->:) where
  o (T f) = fmap (index f . coerceKey)

-- instance HasTrie a => Ob (:->:) a where semiid = T return

instance HasTrie a => Applicative ((:->:) a) where
  pure a = T (pure a)
  T f <*> T g = T (f <*> g)
  a <* _ = a
  _ *> b = b

instance Bind ((:->:) a) where
  T m >>- f = T (tabulate (\a -> index (runT (f (index m a))) a))
  
instance HasTrie a => Monad ((:->:) a) where
  return a = T (return a)
  (>>=) = (>>-)
  _ >> m = m

instance HasTrie a => MonadReader a ((:->:) a) where
  ask = askRep
  local = localRep

instance (HasTrie m, Semigroup m, Monoid m) => Comonad ((:->:) m) where
  extract = flip index mempty

-- TODO: remove dependency on HasTrie
instance (HasTrie m, Semigroup m) => Extend ((:->:) m) where
  duplicate = duplicateRep
