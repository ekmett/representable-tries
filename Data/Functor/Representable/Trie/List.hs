{-# LANGUAGE TypeFamilies #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable.Trie.List
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Data.Functor.Representable.Trie.List ( 
    ListTrie (..) 
  , nil
  , cons
  ) where

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

-- the f-branching stream comonad is the trie of a list 
data ListTrie f a = ListTrie a (f (ListTrie f a)) -- deriving (Eq,Ord,Show,Read)

type instance Key (ListTrie f) = [Key f]

nil :: ListTrie f a -> a
nil (ListTrie x _) = x

cons :: Indexable f => Key f -> ListTrie f a -> ListTrie f a 
cons a (ListTrie _ xs) = index xs a 

instance Functor f => Functor (ListTrie f) where
  fmap f (ListTrie a as) = ListTrie (f a) (fmap (fmap f) as)
-- b <$ _ = pure b

instance Apply f => Apply (ListTrie f) where
  ListTrie a as <.> ListTrie b bs = ListTrie (a b) ((<.>) <$> as <.> bs)
  a <. _ = a
  _ .> b = b

instance Applicative f => Applicative (ListTrie f) where
  pure a = as where as = ListTrie a (pure as)
  ListTrie a as <*> ListTrie b bs = ListTrie (a b) ((<*>) <$> as <*> bs)
  a <* _ = a
  _ *> b = b

instance Representable f => Bind (ListTrie f) where
  (>>-) = bindRep

instance Representable f => Monad (ListTrie f) where
  return = pure
  (>>=) = bindRep
  _ >> a = a

instance Keyed f => Keyed (ListTrie f) where
  mapWithKey f (ListTrie a as) = ListTrie (f [] a) (mapWithKey (\x -> mapWithKey (f . (x:))) as)

instance Foldable f => Foldable (ListTrie f) where
  foldMap f (ListTrie a as) = f a `mappend` foldMap (foldMap f) as

instance Foldable1 f => Foldable1 (ListTrie f) where
  foldMap1 f (ListTrie a as) = f a <> foldMap1 (foldMap1 f) as

instance Traversable f => Traversable (ListTrie f) where
  traverse f (ListTrie a as) = ListTrie <$> f a <*> traverse (traverse f) as

instance Traversable1 f => Traversable1 (ListTrie f) where
  traverse1 f (ListTrie a as) = ListTrie <$> f a <.> traverse1 (traverse1 f) as

instance FoldableWithKey f => FoldableWithKey (ListTrie f) where
  foldMapWithKey f (ListTrie a as) = f [] a `mappend` foldMapWithKey (\x -> foldMapWithKey (f . (x:))) as

instance FoldableWithKey1 f => FoldableWithKey1 (ListTrie f) where
  foldMapWithKey1 f (ListTrie a as) = f [] a <> foldMapWithKey1 (\x -> foldMapWithKey1 (f . (x:))) as

instance TraversableWithKey f => TraversableWithKey (ListTrie f) where
  traverseWithKey f (ListTrie a as) = ListTrie <$> f [] a <*> traverseWithKey (\x -> traverseWithKey (f . (x:))) as

instance TraversableWithKey1 f => TraversableWithKey1 (ListTrie f) where
  traverseWithKey1 f (ListTrie a as) = ListTrie <$> f [] a <.> traverseWithKey1 (\x -> traverseWithKey1 (f . (x:))) as

instance Representable f => Distributive (ListTrie f) where
  distribute = distributeRep

instance Indexable f => Indexable (ListTrie f) where
  index (ListTrie x _) [] = x 
  index (ListTrie _ xs) (a:as) = index (index xs a) as

instance Adjustable f => Adjustable (ListTrie f) where
  adjust f [] (ListTrie x xs) = ListTrie (f x) xs
  adjust f (a:as) (ListTrie x xs) = ListTrie x (adjust (adjust f as) a xs)

instance Lookup f => Lookup (ListTrie f) where
  lookup [] (ListTrie x _) = Just x
  lookup (a:as) (ListTrie _ xs) = lookup a xs >>= lookup as

instance Representable f => Representable (ListTrie f) where
  tabulate f = ListTrie (f []) (tabulate (\x -> tabulate (f . (x:))))
