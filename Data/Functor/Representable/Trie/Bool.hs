{-# LANGUAGE TypeFamilies #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable.Trie.Bool
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Data.Functor.Representable.Trie.Bool ( BoolTrie (..) ) where

import Control.Applicative
import Data.Distributive
import Data.Functor.Representable
import Data.Functor.Bind
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Key
import Prelude hiding (lookup)

-- (Bool, -) -| BoolTrie
data BoolTrie a = BoolTrie a a deriving (Eq,Ord,Show,Read)

false :: BoolTrie a -> a
false (BoolTrie a _) = a

true :: BoolTrie a -> a
true (BoolTrie _ b) = b

type instance Key BoolTrie = Bool

instance Functor BoolTrie where
  fmap f (BoolTrie a b) = BoolTrie (f a) (f b)
  b <$ _ = pure b

instance Apply BoolTrie where
  BoolTrie a b <.> BoolTrie c d = BoolTrie (a c) (b d)
  a <. _ = a
  _ .> b = b

instance Applicative BoolTrie where
  pure a = BoolTrie a a
  (<*>) = (<.>) 
  a <* _ = a
  _ *> b = b

instance Bind BoolTrie where
  BoolTrie a b >>- f = BoolTrie (false (f a)) (true (f b))

instance Monad BoolTrie where
  return = pure
  BoolTrie a b >>= f = BoolTrie (false (f a)) (true (f b))
  _ >> a = a

instance Keyed BoolTrie where
  mapWithKey f (BoolTrie a b) = BoolTrie (f False a) (f True b)

instance Foldable BoolTrie where
  foldMap f (BoolTrie a b) = f a `mappend` f b

instance Foldable1 BoolTrie where
  foldMap1 f (BoolTrie a b) = f a <> f b

instance Traversable BoolTrie where
  traverse f (BoolTrie a b) = BoolTrie <$> f a <*> f b

instance Traversable1 BoolTrie where
  traverse1 f (BoolTrie a b) = BoolTrie <$> f a <.> f b

instance FoldableWithKey BoolTrie where
  foldMapWithKey f (BoolTrie a b) = f False a `mappend` f True b

instance FoldableWithKey1 BoolTrie where
  foldMapWithKey1 f (BoolTrie a b) = f False a <> f True b

instance TraversableWithKey BoolTrie where
  traverseWithKey f (BoolTrie a b) = BoolTrie <$> f False a <*> f True b

instance TraversableWithKey1 BoolTrie where
  traverseWithKey1 f (BoolTrie a b) = BoolTrie <$> f False a <.> f True b

instance Distributive BoolTrie where
  distribute = distributeRep

instance Indexable BoolTrie where
  index (BoolTrie a _) False = a
  index (BoolTrie _ b) True  = b

instance Adjustable BoolTrie where
  adjust f False (BoolTrie a b) = BoolTrie (f a) b
  adjust f True (BoolTrie a b) = BoolTrie a (f b)

instance Lookup BoolTrie where
  lookup = lookupDefault

instance Representable BoolTrie where
  tabulate f = BoolTrie (f False) (f True)
