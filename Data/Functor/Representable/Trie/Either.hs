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

module Data.Functor.Representable.Trie.Either ( 
    EitherTrie (..) 
  , left
  , right
  ) where

import Control.Applicative
import Data.Distributive
import Data.Functor.Representable
import Data.Functor.Bind
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Traversable.Fair
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Key
import Prelude hiding (lookup)

-- the product functor would be the trie of an either, but we fair traversal
data EitherTrie f g a = EitherTrie (f a) (g a)

type instance Key (EitherTrie f g) = Either (Key f) (Key g)

left :: EitherTrie f g a -> f a
left (EitherTrie f _) = f

right :: EitherTrie f g a -> g a 
right (EitherTrie _ g) = g

instance (Apply f, Apply g, Semigroup s) => Semigroup (EitherTrie f g s) where
  EitherTrie a b <> EitherTrie c d = EitherTrie ((<>) <$> a <.> c) ((<>) <$> b <.> d)

instance (Applicative f, Applicative g, Monoid a) => Monoid (EitherTrie f g a) where
  mempty = EitherTrie (pure mempty) (pure mempty)
  EitherTrie a b `mappend` EitherTrie c d = EitherTrie (mappend <$> a <*> c) (mappend <$> b <*> d)
  
instance (Functor f, Functor g) => Functor (EitherTrie f g) where
  fmap f (EitherTrie fs gs) = EitherTrie (fmap f fs) (fmap f gs)
  b <$ EitherTrie fs gs = EitherTrie (b <$ fs) (b <$ gs)

instance (Apply f, Apply g) => Apply (EitherTrie f g) where
  EitherTrie ff fg <.> EitherTrie af ag = EitherTrie (ff <.> af) (fg <.> ag)
  a <. _ = a
  _ .> b = b

instance (Applicative f, Applicative g) => Applicative (EitherTrie f g) where
  pure a = EitherTrie (pure a) (pure a)
  EitherTrie ff fg <*> EitherTrie af ag = EitherTrie (ff <*> af) (fg <*> ag)
  a <* _ = a
  _ *> b = b

-- the direct implementation in terms of Bind is inefficient, using bindRep instead
instance (Representable f, Representable g) => Bind (EitherTrie f g) where
  (>>-) = bindRep

instance (Representable f, Representable g) => Monad (EitherTrie f g) where
  return = pure
  (>>=) = bindRep
  _ >> a = a

instance (Keyed f, Keyed g) => Keyed (EitherTrie f g) where
  mapWithKey f (EitherTrie fs gs) = EitherTrie (mapWithKey (f . Left) fs) (mapWithKey (f . Right) gs)

instance (Foldable f, Foldable g) => Foldable (EitherTrie f g) where
  foldMap f (EitherTrie fs gs) = foldMapBoth f fs gs

instance (Foldable1 f, Foldable1 g) => Foldable1 (EitherTrie f g) where
  foldMap1 f (EitherTrie fs gs) = foldMapBoth1 f fs gs

instance (Traversable f, Traversable g) => Traversable (EitherTrie f g) where
  traverse f (EitherTrie fs gs) = uncurry EitherTrie <$> traverseBoth f fs gs

instance (Traversable1 f, Traversable1 g) => Traversable1 (EitherTrie f g) where
  traverse1 f (EitherTrie fs gs) = uncurry EitherTrie <$> traverseBoth1 f fs gs

instance (FoldableWithKey f, FoldableWithKey g) => FoldableWithKey (EitherTrie f g) where
  foldMapWithKey f (EitherTrie fs gs) = foldMapWithKeyBoth (f . Left) (f . Right) fs gs

instance (FoldableWithKey1 f, FoldableWithKey1 g) => FoldableWithKey1 (EitherTrie f g) where
  foldMapWithKey1 f (EitherTrie fs gs) = foldMapWithKeyBoth1 (f . Left) (f . Right) fs gs

instance (TraversableWithKey f, TraversableWithKey g) => TraversableWithKey (EitherTrie f g) where
  traverseWithKey f (EitherTrie fs gs) = uncurry EitherTrie <$> traverseWithKeyBoth (f . Left) (f . Right) fs gs

instance (TraversableWithKey1 f, TraversableWithKey1 g) => TraversableWithKey1 (EitherTrie f g) where
  traverseWithKey1 f (EitherTrie fs gs) = uncurry EitherTrie <$> traverseWithKeyBoth1 (f . Left) (f . Right) fs gs

instance (Representable f, Representable g) => Distributive (EitherTrie f g) where
  distribute = distributeRep

instance (Indexable f, Indexable g) => Indexable (EitherTrie f g) where
  index (EitherTrie fs _) (Left  i) = index fs i
  index (EitherTrie _ gs) (Right j) = index gs j

instance (Adjustable f, Adjustable g) => Adjustable (EitherTrie f g) where
  adjust f (Left i) (EitherTrie fs gs)  = EitherTrie (adjust f i fs) gs
  adjust f (Right j) (EitherTrie fs gs) = EitherTrie fs (adjust f j gs)

instance (Lookup f, Lookup g) => Lookup (EitherTrie f g) where
  lookup (Left i) (EitherTrie fs _)  = lookup i fs
  lookup (Right j) (EitherTrie _ gs) = lookup j gs

instance (Representable f, Representable g) => Representable (EitherTrie f g) where
  tabulate f = EitherTrie (tabulate (f . Left)) (tabulate (f . Right))
