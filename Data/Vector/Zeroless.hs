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
  , 

import Control.Applicative
import Data.Distributive
import Data.Functor.Representable
import Data.Functor.Bind
import Data.Foldable
import Data.Bifoldable
import Data.Function (on)
import Data.Monoid
import Data.Traversable
import Data.Bitraversable
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Key
import Prelude hiding (lookup)

-- each vector memoizes the size of its _child_ vectors for efficiency
data Vector n a where
  V0 :: Vector D0 a
  V1 :: a -> Vector n (a,a) -> Vector (D1 n) a
  V2 :: a -> a -> Vector n (a,a) -> Vector (D2 n) a

infixr 5 <|

type Key (Vector n) = Fin n

(<|) :: a -> Vector n a -> Vector (Succ n) a
a <| V0 = V1 a V0 V0
a <| V1 b t = V2 a b t
a <| V2 b c t = V1 a ((b,c) <| t)

class NonEmpty n where
  tail :: Vector n a -> Vector (Pred n) a)
  uncons :: Vector n a -> (a, Vector n a)
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
    V1{} -> f (Fin 0) a <> foldMapWithKey1' (\k (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t
    V2{} -> f (Fin 0) a <> foldMapWithKey1' (\k (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t

  traverseWithKey1' f (V1 a t) = case t of
    V0 -> flip V1 V0 <$> f 0 a
    V1{} -> V1 <$> f (Fin 0) a <.> traverseWithKey1' (\k (l,r) -> (,) <$> f (Fin (2*k+1)) l <.> f (Fin (2*k+2)) r) t
    V2{} -> V1 <$> f (Fin 0) a <.> traverseWithKey1' (\k (l,r) -> (,) <$> f (Fin (2*k+1)) l <.> f (Fin (2*k+2)) r) t

instance NonEmpty (D2 n) where
  tail (V2 _ b t) = V1 b t

  uncons (V2 a b t) = (a, V1 b t)

  head (V2 a _ _) = a

  foldMap1' f (V2 a b t) = case t of
    V0 -> f a <> f b
    V1{} -> f a <> f b <> foldMap1' (\(l,r) -> f l <> f r) t
    V2{} -> f a <> f b <> foldMap1' (\(l,r) -> f l <> f r) t

  traverse1' f (V2 a b t) = case t of
    V0   -> (\x y -> V2 a b V0) <$> f a <.> f b
    V1{} -> V1 <$> f a <.> f b <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t
    V2{} -> V1 <$> f a <.> f b <.> traverse1' (\(l,r) -> (,) <$> f l <.> f r) t

  foldMapWithKey1' f (V2 a b t) = case t of
    V0 -> f (Fin 0) a <> f (Fin 1) b
    V1{} -> f (Fin 0) a <> f (Fin 1) b <> foldMapWithKey1' (\k (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t
    V2{} -> f (Fin 0) a <> f (Fin 1) b <> foldMapWithKey1' (\k (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t

  traverseWithKey1' f (V2 a b t) = case t of
    V0 -> (\x y -> V2 a b V0) <$> f (Fin 0) a <.> f (Fin 1) a
    V1{} -> V1 <$> f (Fin 0) a <.> f (Fin 1) b <.> traverseWithKey1' (\(Fin k) (l,r) -> (,) <$> f (Fin (2*k+2)) l <.> f (Fin (2*k+3)) r) t
    V2{} -> V1 <$> f (Fin 0) a <.> f (Fin 1) b <.> traverseWithKey1' (\k (l,r) -> (,) <$> f (Fin (2*k+2)) l <.> f (Fin (2*k+3)) r) t

size :: Vector n a -> Int
size V0 = 0 
size (V1 _ t) = 2 * size t + 1
size (V2 _ _ t) = 2 * size t + 2

instance Functor (Vector n) where
  fmap _ V0 = V0
  fmap f (V1 a x y)   = V1 (f a) (fmap f x) (fmap f y)
  fmap f (V2 a b x y) = V2 (f a) (f b) (fmap f x) (fmap f y)

instance Apply (Vector n) where
  V0 <.> V0 = V0
  V1 a s <.> V1 b t = V1 (a b) (\(w,x) (y,z) -> (w y, x z) <$> s <.> t)
  V2 a b s <.> V2 c d t = V2 (a b) (c d) (\(w,x) (y,z) -> (w y, x z) <$> s <.> t)

instance Representable (Vector n) => Applicative (Vector n) where
  V0 <*> V0 = V0
  V1 a s <*> V1 b t = V1 (a b) (\(w,x) (y,z) -> (w y, x z) <$> s <*> t)
  V2 a b s <*> V2 c d t = V2 (a b) (c d) (\(w,x) (y,z) -> (w y, x z) <$> s <*> t)

instance Representable (Vector n) => Bind (Vector n) where
  (>>-) = bindRep

instance Representable (Vector n) => Monad (Vector n) where
  (>>=) = bindRep
  
instance Keyed (Vector n) where
  mapWithKey _ V0 = V0
  mapWithKey f (V1 n a x y) = V1 n (f (Fin 0) a) 
    (mapWithKey (f . Fin . (+1) . getFin) x)
    (mapWithKey (f . Fin . (+1+n) . getFin) y)
  mapWithKey f (V2 n a b x y) = V2 n (f (Fin 0) a) (f (Fin 1) b)
    (mapWithKey (f . Fin . (+2) . getFin) x)
    (mapWithKey (f . Fin . (+2+n) . getFin) y)

instance Indexable (Vector n) where
  index (V1 a t) (Fin 0) = a
  index (V1 a t@V1{}) (Fin n) = case quotRem (n - 1) of
    (q,0) -> fst (index t (Fin q))
    (q,_) -> snd (index t (Fin q))
  index (V2 a _ _) (Fin 0) = a
  index (V2 _ b _) (Fin 1) = b
  index (V2 _ _ t) (Fin n) = case quotRem (n - 2) of
    (q,0) -> fst (index t (Fin q))
    (q,_) -> snd (index t (Fin q))
  index _ _ = error "index: illegal"

instance Adjustable (Vector n) where
  adjust _ _ V0 = V0
  adjust f (Fin 0) (V1 a t) = V1 (f a) t
  adjust f (Fin n) (V1 a t) = case quotRem (n - 1) of
    (q,0) -> V1 a (adjust (first f) (Fin q) t)
    (q,_) -> V1 a (adjust (second f) (Fin q) t)
  adjust f (Fin 0) (V2 a b t) = V1 (f a) b t
  adjust f (Fin 1) (V2 a b t) = V1 a (f b) t
  adjust f (Fin n) (V2 a b t) = case quotRem (n - 2) of
    (q,0) -> V2 a b (adjust (first f) (Fin q) t)
    (q,_) -> V2 a b (adjust (second f) (Fin q) t)

instance Foldable (Vector n) where
  foldMap _ V0 = mempty
  foldMap f (V1 a t) = f a `mappend` foldMap (\(l,r)uncurry (mappend `on` f)) t
  foldMap f (V2 a b t) = f a `mappend` f b `mappend` foldMap (bifoldMap f f) t 

instance NonEmpty n => Foldable1 (Vector n) where
  foldMap1 = foldMap1' 

instance Traversable (Vector n) where
  traverse _ V0 = pure V0
  traverse f (V1 a t) = V1 <$> f a <*> traverse (\(l,r) -> (,) <$> f l <*> f r) t
  traverse f (V2 a b t) = V2 <$> f a <*> f b <*> traverse (\(l,r) -> (,) <$> f l <*> f r) t

instance NonEmpty n => Traversable1 (Vector n) where
  traverse1 = traverse1'

instance FoldableWithKey (Vector n) where
  foldMapWithKey _ V0 = pure V0
  foldMapWithKey f (V1 a t) = f (Fin 0) a <> foldMapWithKey (\k (l,r) -> f (Fin (2*k+1)) l <> f (Fin (2*k+2)) r) t
  foldMapWithKey f (V2 a b t) = f (Fin 0) a <> f (Fin 1) b <> foldMapWithKey (\k (l,r) -> f (Fin (2*k+2)) l <> f (Fin (2*k+3)) r) t

instance NonEmpty n => FoldableWithKey1 (Vector n) where
  foldMapWithKey1 = foldMapWithKey1'

instance TraversableWithKey (Vector n) where
  traverseWithKey _ V0 = pure V0
  traverseWithKey f (V1 a t) = V1 <$> f (Fin 0) a <*> traverseWithKey (\k (l,r) -> (,) <$> f (Fin (2*k+1)) l <*> f (Fin (2*k+2)) r) t
  traverseWithKey f (V2 a b t) = V2 <$> f (Fin 0) a <*> f (Fin 1) b <*> traverseWithKey (\k (l,r) -> (,) <$> f (Fin (2*k+2)) l <*> f (Fin (2*k+3)) r) t

instance NonEmpty n => TraversableWithKey1 (Vector n) where
  traverseWithKey1 = traverseWithKey1'

instance Representable (Vector n) => Distributive (Vector n) where
  distribute = distributeRep

instance Representable (Vector D0) where
  tabulate _ = V0

instance Representable (Vector n) => Representable (Vector (D1 n)) where
  tabulate f = V1 (f (Fin 0)) $ tabulate $ \k -> (f (2*k+1), f (2*k+2))
  
instance Representable (Vector n) => Representable (Vector (D2 n)) where
  tabulate f = V2 (f (Fin 0)) (f (Fin 1)) $ tabulate $ \k -> (f (2*k+2), f (2*k+3))
