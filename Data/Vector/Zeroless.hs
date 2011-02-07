{-# LANGUAGE TypeFamilies, Rank2Types, TypeOperators, GADTs, EmptyDataDecls, FlexibleInstances, FlexibleContexts, UndecidableInstances  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Vector.Zeroless
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
-- Fixed-length Vectors with zeroless binary indexing
----------------------------------------------------------------------

module Data.Vector.Zeroless 
  ( Vector
  , (<|) 
  , NonEmpty(tail,head,uncons)
  , size
  ) where

import Control.Arrow
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
import Numeric.Nat.Zeroless
import Prelude hiding (lookup, tail, head)

-- each vector memoizes the size of its _child_ vectors for efficiency
data Vector n a where
  V0 :: Vector D0 a
  V1 :: a -> Vector n (a,a) -> Vector (D1 n) a
  V2 :: a -> a -> Vector n (a,a) -> Vector (D2 n) a

infixr 5 <|

type instance Key (Vector n) = Fin n

(<|) :: a -> Vector n a -> Vector (Succ n) a
a <| V0 = V1 a V0
a <| V1 b t = V2 a b t
a <| V2 b c t = V1 a ((b,c) <| t)

class NonEmpty n where
  tail :: Vector n a -> Vector (Pred n) a
  uncons :: Vector n a -> (a, Vector (Pred n) a)
  head :: Vector n a -> a

  foldMap1' :: Semigroup m => (a -> m) -> Vector n a -> m
  traverse1' :: Apply t => (a -> t b) -> Vector n a -> t (Vector n b)
  foldMapWithKey1' :: Semigroup m => (Fin n -> a -> m) -> Vector n a -> m
  traverseWithKey1' :: Apply t => (Fin n -> a -> t b) -> Vector n a -> t (Vector n b)

instance NonEmpty (D1 n) where
  tail (V1 _ V0) = V0
  tail (V1 _ (V2 (b,c) de t)) = V2 b c (V1 de t)
  tail (V1 _ v1@(V1 (b,c) _)) = V2 b c (tail v1)

  uncons (V1 a V0) = (a, V0)
  uncons (V1 a v1@(V1 (b,c) _)) = (a, V2 b c (tail v1))
  uncons (V1 a (V2 (b,c) de t)) = (a, V2 b c (V1 de t))

  head (V1 a _) = a

  foldMap1' f (V1 a t) = case t of
    V0 -> f a
    V1{} -> f a <> foldMap1' (\(l,r) -> f l <> f r) t
    V2{} -> f a <> foldMap1' (\(l,r) -> f l <> f r) t

  traverse1' f (V1 a t) = case t of
    V0 -> flip V1 V0 <$> f a 
    V1{} -> V1 <$> f a <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t
    V2{} -> V1 <$> f a <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t
    
  foldMapWithKey1' f (V1 a t) = case t of
    V0 -> f (Fin 0) a
    V1{} -> f (Fin 0) a <> foldMapWithKey1' (\(Fin k) (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t
    V2{} -> f (Fin 0) a <> foldMapWithKey1' (\(Fin k) (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t

  traverseWithKey1' f (V1 a t) = case t of
    V0 -> flip V1 V0 <$> f 0 a
    V1{} -> V1 <$> f (Fin 0) a <.> traverseWithKey1' (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+1)) l <.> f (Fin (2*k+2)) r) t
    V2{} -> V1 <$> f (Fin 0) a <.> traverseWithKey1' (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+1)) l <.> f (Fin (2*k+2)) r) t

instance NonEmpty (D2 n) where
  tail (V2 _ b t) = V1 b t

  uncons (V2 a b t) = (a, V1 b t)

  head (V2 a _ _) = a

  foldMap1' f (V2 a b t) = case t of
    V0 -> f a <> f b
    V1{} -> f a <> f b <> foldMap1' (\(l,r) -> f l <> f r) t
    V2{} -> f a <> f b <> foldMap1' (\(l,r) -> f l <> f r) t

  traverse1' f (V2 a b t) = case t of
    V0   -> (\x y -> V2 x y V0) <$> f a <.> f b
    V1{} -> V2 <$> f a <.> f b <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t
    V2{} -> V2 <$> f a <.> f b <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t

  foldMapWithKey1' f (V2 a b t) = case t of
    V0 -> f (Fin 0) a <> f (Fin 1) b
    V1{} -> f (Fin 0) a <> f (Fin 1) b <> foldMapWithKey1' (\(Fin k) (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t
    V2{} -> f (Fin 0) a <> f (Fin 1) b <> foldMapWithKey1' (\(Fin k) (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t

  traverseWithKey1' f (V2 a b t) = case t of
    V0 -> (\x y -> V2 x y V0) <$> f (Fin 0) a <.> f (Fin 1) a
    V1{} -> V2 <$> f (Fin 0) a <.> f (Fin 1) b <.> traverseWithKey1' (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+2)) l <.> f (Fin (2*k+3)) r) t
    V2{} -> V2 <$> f (Fin 0) a <.> f (Fin 1) b <.> traverseWithKey1' (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+2)) l <.> f (Fin (2*k+3)) r) t

size :: Vector n a -> Int
size V0 = 0 
size (V1 _ t) = 2 * size t + 1
size (V2 _ _ t) = 2 * size t + 2

instance Functor (Vector n) where
  fmap _ V0 = V0
  fmap f (V1 a t)   = V1 (f a) $ fmap (f *** f) t
  fmap f (V2 a b t) = V2 (f a) (f b) $ fmap (f *** f) t
  _ <$ V0 = V0
  b <$ V1 _ t = V1 b $ (b,b) <$ t
  b <$ V2 _ _ t = V2 b b $ (b,b) <$ t

instance Apply (Vector n) where
  V0 <.> V0 = V0
  V1 a s <.> V1 b t = V1 (a b) $ (\(w,x) (y,z) -> (w y, x z)) <$> s <.> t
  V2 a b s <.> V2 c d t = V2 (a c) (b d) $ (\(w,x) (y,z) -> (w y, x z)) <$> s <.> t
  _ <.> _ = error "GADT fail"
  a <. _ = a
  _ .> a = a

instance Applicative (Vector D0) where
  pure _ = V0
  V0 <*> V0 = V0
  a <* _ = a
  _ *> a = a

instance Applicative (Vector n) => Applicative (Vector (D1 n)) where
  pure a = V1 a $ pure (a,a)
  V1 a s <*> V1 b t = V1 (a b) $ (\(w,x) (y,z) -> (w y, x z)) <$> s <*> t
  a <* _ = a
  _ *> a = a

instance Applicative (Vector n) => Applicative (Vector (D2 n)) where
  pure a = V2 a a $ pure (a,a)
  V2 a b s <*> V2 c d t = V2 (a c) (b d) $ (\(w,x) (y,z) -> (w y, x z)) <$> s <*> t
  a <* _ = a
  _ *> a = a

{-
instance Representable (Vector n) => Bind (Vector n) where
  (>>-) = bindRep

instance Representable (Vector n) => Monad (Vector n) where
  (>>=) = bindRep
  _ >> a = a
-}
  
instance Keyed (Vector n) where
  mapWithKey _ V0 = V0
  mapWithKey f (V1 a t) = V1 (f (Fin 0) a) $
    mapWithKey (\(Fin k) (l,r) -> (f (Fin (2*k+1)) l, f (Fin (2*k+2)) r)) t
  mapWithKey f (V2 a b t) = V2 (f (Fin 0) a) (f (Fin 1) b) $ 
    mapWithKey (\(Fin k) (l,r) -> (f (Fin (2*k+2)) l, f (Fin (2*k+3)) r)) t

instance Indexable (Vector n) where
  index (V1 a _) (Fin 0) = a
  index (V1 _ t) (Fin n) = case quotRem (n - 1) 2 of
    (q,0) -> fst (index t (Fin q))
    (q,_) -> snd (index t (Fin q))
  index (V2 a _ _) (Fin 0) = a
  index (V2 _ b _) (Fin 1) = b
  index (V2 _ _ t) (Fin n) = case quotRem (n - 2) 2 of
    (q,0) -> fst (index t (Fin q))
    (q,_) -> snd (index t (Fin q))
  index _ _ = error "index: illegal"

instance Adjustable (Vector n) where
  adjust _ _ V0 = V0
  adjust f (Fin 0) (V1 a t) = V1 (f a) t
  adjust f (Fin n) (V1 a t) = case quotRem (n - 1) 2 of
    (q,0) -> V1 a (adjust (first f) (Fin q) t)
    (q,_) -> V1 a (adjust (second f) (Fin q) t)
  adjust f (Fin 0) (V2 a b t) = V2 (f a) b t
  adjust f (Fin 1) (V2 a b t) = V2 a (f b) t
  adjust f (Fin n) (V2 a b t) = case quotRem (n - 2) 2 of
    (q,0) -> V2 a b (adjust (first f) (Fin q) t)
    (q,_) -> V2 a b (adjust (second f) (Fin q) t)

instance Foldable (Vector n) where
  foldMap _ V0 = mempty
  foldMap f (V1 a t) = f a `mappend` foldMap (\(l,r) -> f l `mappend` f r) t
  foldMap f (V2 a b t) = f a `mappend` f b `mappend` foldMap (\(l, r) -> f l `mappend` f r) t 

instance NonEmpty n => Foldable1 (Vector n) where
  foldMap1 = foldMap1' 

instance Traversable (Vector n) where
  traverse _ V0 = pure V0
  traverse f (V1 a t) = V1 <$> f a <*> traverse (\(l,r) -> (,) <$> f l <*> f r) t
  traverse f (V2 a b t) = V2 <$> f a <*> f b <*> traverse (\(l,r) -> (,) <$> f l <*> f r) t

instance NonEmpty n => Traversable1 (Vector n) where
  traverse1 = traverse1'

instance FoldableWithKey (Vector n) where
  foldMapWithKey _ V0 = mempty
  foldMapWithKey f (V1 a t) = f (Fin 0) a `mappend` foldMapWithKey (\(Fin k) (l,r) -> f (Fin (2*k+1)) l `mappend` f (Fin (2*k+2)) r) t
  foldMapWithKey f (V2 a b t) = f (Fin 0) a `mappend` f (Fin 1) b `mappend` foldMapWithKey (\(Fin k) (l,r) -> f (Fin (2*k+2)) l `mappend` f (Fin (2*k+3)) r) t

instance NonEmpty n => FoldableWithKey1 (Vector n) where
  foldMapWithKey1 = foldMapWithKey1'

instance TraversableWithKey (Vector n) where
  traverseWithKey _ V0 = pure V0
  traverseWithKey f (V1 a t) = V1 <$> f (Fin 0) a <*> traverseWithKey (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+1)) l <*> f (Fin (2*k+2)) r) t
  traverseWithKey f (V2 a b t) = V2 <$> f (Fin 0) a <*> f (Fin 1) b <*> traverseWithKey (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+2)) l <*> f (Fin (2*k+3)) r) t

instance NonEmpty n => TraversableWithKey1 (Vector n) where
  traverseWithKey1 = traverseWithKey1'

instance Representable (Vector n) => Distributive (Vector n) where
  distribute = distributeRep

instance Representable (Vector D0) where
  tabulate _ = V0

instance Representable (Vector n) => Representable (Vector (D1 n)) where
  tabulate f = V1 (f (Fin 0)) $ tabulate $ \(Fin k) -> (f (Fin (2*k+1)), f (Fin (2*k+2)))
  
instance Representable (Vector n) => Representable (Vector (D2 n)) where
  tabulate f = V2 (f (Fin 0)) (f (Fin 1)) $ tabulate $ \(Fin k) -> (f (Fin (2*k+2)), f (Fin (2*k+3)))
