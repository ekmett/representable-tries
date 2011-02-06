module Data.Traversable.Fair 
  ( foldMapBoth
  , traverseBoth
  , foldMapWithKeyBoth
  , traverseWithKeyBoth
  , foldMapBoth1
  , traverseBoth1
  , foldMapWithKeyBoth1
  , traverseWithKeyBoth1
  ) where

import Control.Applicative
import Control.Arrow
import Data.Key
import Data.Functor.Apply
import Data.Function (on)
import Data.Monoid
import Data.Stream.NonEmpty as NonEmpty hiding (toList)
import Data.Foldable

-- placeholder instances
instance Foldable1 NonEmpty
instance Traversable1 NonEmpty

refill :: Traversable t => t a -> [b] -> t b
refill t l = snd (mapAccumL (\(x:xs) _ -> (xs, x)) l t)

toNonEmptyList :: Foldable1 f => f a -> NonEmpty a
toNonEmptyList = NonEmpty.fromList . toList

toKeyedNonEmptyList :: FoldableWithKey1 f => f a -> NonEmpty (Key f, a)
toKeyedNonEmptyList = NonEmpty.fromList . toKeyedList

foldMapBoth :: (Foldable f, Foldable g, Monoid m) => (a -> m) -> f a -> g a -> m
foldMapBoth f as bs = go (toList as) (toList bs) where
  go [] [] = mempty
  go xs [] = foldMap f xs
  go [] ys = foldMap f ys
  go (x:xs) (y:ys) = f x `mappend` f y `mappend` go xs ys

-- | traverse both containers, interleaving effects for fairness
traverseBoth :: (Traversable f, Traversable g, Applicative m) => (a -> m b) -> f a -> g a -> m (f b, g b)
traverseBoth f as bs = (refill as *** refill bs) <$> go (toList as) (toList bs)
  where
  go [] []         = pure ([],[])
  go xs []         = flip (,) [] <$> traverse f xs
  go [] ys         = (,) [] <$> traverse f ys
  go (x:xs) (y:ys) = (\x y (xs,ys) -> (x:xs,y:ys)) <$> f x <*> f y <*> go xs ys

-- | fold both containers, interleaving results for fairness
foldMapBoth1 :: (Foldable1 f, Foldable1 g, Semigroup m) => (a -> m) -> f a -> g a -> m
foldMapBoth1 f as bs = go (toNonEmptyList as) (toNonEmptyList bs)
  where
  go (x:|[])   (y:|[])   = f x <> f y
  go (x:|z:zs) (y:|[])   = f x <> f y <> foldMap1 f (z:|zs)
  go (x:|[])   ys        = f x <> foldMap1 f ys
  go (x:|z:zs) (y:|w:ws) = f x <> f y <> go (z:|zs) (w:|ws)

-- | traverse both containers, interleaving effects for fairness
traverseBoth1 :: (Traversable1 f, Traversable1 g, Apply m) => (a -> m b) -> f a -> g a -> m (f b, g b)
traverseBoth1 f as bs = (refill as *** refill bs) <$> go (toNonEmptyList as) (toNonEmptyList bs)
  where
  go (x:|[])   (y:|[])   = (\x' y'            -> ([x'],       [y']  )) <$> f x <.> f y
  go (x:|z:zs) (y:|[])   = (\x' y' (x'':|xs') -> (x':x'':xs', [y']  )) <$> f x <.> f y <.> traverse1 f (z:|zs)
  go (x:|[])   ys        = (\x' (y':|ys')     -> ([x'],       y':ys')) <$> f x <.> traverse1 f ys
  go (x:|z:zs) (y:|w:ws) = (\x' y' (xs', ys') -> (x':xs',     y':ys')) <$> f x <.> f y <.> go (z:|zs) (w:|ws)

foldMapWithKeyBoth 
  :: (FoldableWithKey f, FoldableWithKey g, Monoid m) 
  => (Key f -> a -> m) 
  -> (Key g -> a -> m)
  -> f a 
  -> g a 
  -> m
foldMapWithKeyBoth f g as bs = go (toKeyedList as) (toKeyedList bs) where
  f' = uncurry f
  g' = uncurry g
  go [] [] = mempty
  go xs [] = foldMap f' xs
  go [] ys = foldMap g' ys
  go (x:xs) (y:ys) = f' x `mappend` g' y `mappend` go xs ys

-- | traverse both containers, interleaving effects for fairness
traverseWithKeyBoth 
  :: (TraversableWithKey f, TraversableWithKey g, Applicative m) 
  => (Key f -> a -> m b) 
  -> (Key g -> a -> m b) 
  -> f a 
  -> g a 
  -> m (f b, g b)
traverseWithKeyBoth f g as bs = (refill as *** refill bs) <$> go (toKeyedList as) (toKeyedList bs)
  where
  f' = uncurry f
  g' = uncurry g
  go [] []         = pure ([],[])
  go xs []         = flip (,) [] <$> traverse f' xs
  go [] ys         = (,) [] <$> traverse g' ys
  go (x:xs) (y:ys) = (\x y (xs,ys) -> (x:xs,y:ys)) <$> f' x <*> g' y <*> go xs ys

-- | fold both containers, interleaving results for fairness
foldMapWithKeyBoth1 
  :: (FoldableWithKey1 f, FoldableWithKey1 g, Semigroup m) 
  => (Key f -> a -> m) 
  -> (Key g -> a -> m) 
  -> f a 
  -> g a 
  -> m
foldMapWithKeyBoth1 f g as bs = go (toKeyedNonEmptyList as) (toKeyedNonEmptyList bs)
  where
  f' = uncurry f
  g' = uncurry g
  go (x:|[])   (y:|[])   = f' x <> g' y
  go (x:|z:zs) (y:|[])   = f' x <> g' y <> foldMap1 f' (z:|zs)
  go (x:|[])   ys        = f' x <> foldMap1 g' ys
  go (x:|z:zs) (y:|w:ws) = f' x <> g' y <> go (z:|zs) (w:|ws)

-- | traverse both containers, interleaving effects for fairness
traverseWithKeyBoth1 
  :: (TraversableWithKey1 f, TraversableWithKey1 g, Apply m) 
  => (Key f -> a -> m b) 
  -> (Key g -> a -> m b) 
  -> f a 
  -> g a 
  -> m (f b, g b)
traverseWithKeyBoth1 f g as bs = (refill as *** refill bs) <$> go (toKeyedNonEmptyList as) (toKeyedNonEmptyList bs)
  where
  f' = uncurry f
  g' = uncurry g
  go (x:|[])   (y:|[])   = (\x' y'            -> ([x'],      [y']  )) <$> f' x <.> g' y
  go (x:|z:zs) (y:|[])   = (\x' y' (z':|zs')  -> (x':z':zs', [y']  )) <$> f' x <.> g' y <.> traverse1 f' (z:|zs)
  go (x:|[])   ys        = (\x' (y':|ys')     -> ([x'],      y':ys')) <$> f' x <.> traverse1 g' ys
  go (x:|z:zs) (y:|w:ws) = (\x' y' (xs', ys') -> (x':xs',    y':ys')) <$> f' x <.> g' y <.> go (z:|zs) (w:|ws)
