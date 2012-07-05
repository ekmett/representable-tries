{-# LANGUAGE TypeFamilies #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable.Trie.Vector
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- a trie for zeroless-binary vectors
----------------------------------------------------------------------

module Data.Functor.Representable.Trie.Vector ( 
    VectorTrie (..) 
  ) where

import Control.Applicative
import Data.Distributive
import Data.Functor.Representable
import Data.Functor.Bind
import Data.Foldable
import Data.Traversable
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Key
import Prelude hiding (lookup)

data VectorTrie f n a where
  T0 :: a -> VectorTrie D0 
  T1 :: f (VectorTrie (Product f f) n a) -> VectorTrie f (D1 n a)
  T2 :: f (f (VectorTrie (Product f f) n a)) -> VectorTrie f (D2 n a)

type instance Key (VectorTrie n f) = Vector n (Key f)

instance Functor f => Functor (VectorTrie f) where
  fmap f (T0 a) = T0 (f a)
-- TODO: fix below here
  fmap f (T1 as) = T1 (fmap (fmap f) as)
  fmap f (T2 ass) = T1 (fmap (fmap (fmap f)) as)
-- b <$ _ = pure b

instance Apply f => Apply (VectorTrie f) where
  T0 a <.> T0 b = T0
  T1 as <.> T1 bs = T1 ((<.>) <$> as <.> bs) 
  T2 ass <.> T2 bss = T1 (liftF2 (<.>) <$> as <.> bs) 
  a <. _ = a
  _ .> b = b

instance Applicative (VectorTrie f D0) where
  pure a = T0 a
  T0 a <*> T0 b = T0 (a b)
  a <* _ = a
  _ *> a = a
  
instance (Applicative f, Applicative (VectorTrie f n)) => Applicative (VectorTrie f (D1 n)) where
  pure a = T1 (pure (pure a))
  T1 as <*> T1 bs = T ((<*>) <$> as <*> bs)
  a <* _ = a
  _ *> a = a

instance (Applicative f, Applicative (VectorTrie f n)) => Applicative (VectorTrie f (D1 n)) where
  pure a = T2 (pure (pure (pure a))
  T2 ass <*> T2 bss = T1 (liftA2 (<*>) <$> as <*> bs) 
  a <* _ = a
  _ *> a = a
{-
instance Representable f => Bind (ListTrie f) where
  (>>-) = bindRep

instance Representable f => Monad (ListTrie f) where
  return = pure
  (>>=) = bindRep
  _ >> a = a
-}

instance Keyed f => Keyed (VectorTrie f n) where
  mapWithKey f (T0 a) = T0 (f V0 a)
  mapWithKey f (T1 as) = T1 (mapWithKey (\x -> mapWihKey (f . V1 

ListTrie (f [] a) (mapWithKey (\x -> mapWithKey (f . (x:))) as)

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
