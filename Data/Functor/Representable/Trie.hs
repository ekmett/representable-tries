{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Representable.Trie
-- Copyright   :  (c) Edward Kmett 2011
-- License     :  BSD3
-- 
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- 
----------------------------------------------------------------------

module Data.Functor.Representable.Trie
  ( 
  -- * Representations of polynomial functors
    HasTrie(..)
  -- * Memoizing functions
  , mup, memo, memo2, memo3
  , inTrie, inTrie2, inTrie3
  -- * Workarounds for current GHC limitations
  , trie, untrie
  , (:->:)(..)
  , Entry(..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Representable.Reader
import Data.Bits
import Data.Distributive
import Data.Semigroup
import Data.Word
import Data.Int
import Data.Foldable
import Data.Function (on)
import Data.Functor.Adjunction
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Functor.Representable.Trie.Bool
import Data.Functor.Representable.Trie.Either
import Data.Functor.Representable.Trie.List
import Data.Key
import qualified Data.Monoid as Monoid
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Sequence (Seq, (<|))
import qualified Data.Sequence as Seq
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Traversable
import Prelude hiding (lookup, foldr)

class (Adjustable (BaseTrie a), TraversableWithKey1 (BaseTrie a), Representable (BaseTrie a)) => HasTrie a where
  type BaseTrie a :: * -> *
  -- projectKey . embedKey = id
  embedKey   :: a -> Key (BaseTrie a)
  projectKey :: Key (BaseTrie a) -> a
{-
  validKey   :: Key (BaseTrie a) -> Bool
  validKey _ = True
-}

newtype a :->: b = Trie { runTrie :: BaseTrie a b } 

type instance Key ((:->:) a) = a

data Entry a b = Entry a b

-- * Combinators

-- Matt Hellige's notation for @argument f . result g@.
-- <http://matt.immute.net/content/pointless-fun>
(~>) :: (a' -> a) -> (b -> b') -> (a -> b) -> a' -> b'
g ~> f = (f .) . (. g)

untrie :: HasTrie t => (t :->: a) -> t -> a
untrie = index

trie :: HasTrie t => (t -> a) -> (t :->: a)
trie = tabulate

{-# RULES
"trie/untrie" forall t. trie (untrie t) = t
"embedKey/projectKey" forall t. projectKey (embedKey t) = t
 #-}

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
  -> (a :->: b) -> c :->: d
inTrie = untrie ~> trie

-- | Apply a binary function inside of a tabulate
inTrie2 
  :: (HasTrie a, HasTrie c, HasTrie e) 
  => ((a -> b) -> (c -> d) -> e -> f)
  -> (a :->: b) -> (c :->: d) -> e :->: f
inTrie2 = untrie ~> inTrie

-- | Apply a ternary function inside of a tabulate
inTrie3 
  :: (HasTrie a, HasTrie c, HasTrie e, HasTrie g) 
  => ((a -> b) -> (c -> d) -> (e -> f) -> g -> h)
  -> (a :->: b) -> (c :->: d) -> (e :->: f) -> g :->: h
inTrie3 = untrie ~> inTrie2

-- * Implementation details

instance Functor (Entry a) where
  fmap f (Entry a b) = Entry a (f b)

instance HasTrie e => Lookup ((:->:)e) where
  lookup = lookupDefault

instance HasTrie e => Indexable ((:->:)e) where
  index (Trie f) = index f . embedKey

instance HasTrie e => Distributive ((:->:) e) where
  distribute = distributeRep

instance HasTrie e => Representable ((:->:) e) where
  tabulate f = Trie $ tabulate (f . projectKey)

instance HasTrie e => Adjustable ((:->:) e) where
  adjust f k (Trie as) = Trie (adjust f (embedKey k) as)

instance HasTrie e => Zip ((:->:) e)

instance HasTrie e => ZipWithKey ((:->:) e) 

instance HasTrie e => Adjunction (Entry e) ((:->:) e) where
  unit = mapWithKey Entry . pure
  counit (Entry a t) = index t a

instance HasTrie a => Functor ((:->:) a) where
  fmap f (Trie g) = Trie (fmap f g)

instance HasTrie a => Keyed ((:->:) a) where
  mapWithKey f (Trie a) = Trie (mapWithKey (f . projectKey) a)

instance HasTrie a => Foldable ((:->:) a) where
  foldMap f (Trie a) = foldMap f a

instance HasTrie a => FoldableWithKey ((:->:) a) where
  foldMapWithKey f (Trie a) = foldMapWithKey (f . projectKey) a

instance HasTrie a => Traversable ((:->:) a) where
  traverse f (Trie a) = Trie <$> traverse f a

instance HasTrie a => TraversableWithKey ((:->:) a) where
  traverseWithKey f (Trie a) = Trie <$> traverseWithKey (f . projectKey) a

instance HasTrie a => Foldable1 ((:->:) a) where
  foldMap1 f (Trie a) = foldMap1 f a

instance HasTrie a => FoldableWithKey1 ((:->:) a) where
  foldMapWithKey1 f (Trie a) = foldMapWithKey1 (f . projectKey) a

instance HasTrie a => Traversable1 ((:->:) a) where
  traverse1 f (Trie a) = Trie <$> traverse1 f a

instance HasTrie a => TraversableWithKey1 ((:->:) a) where
  traverseWithKey1 f (Trie a) = Trie <$> traverseWithKey1 (f . projectKey) a

instance (HasTrie a, Eq b) => Eq (a :->: b) where
  (==) = (==) `on` toList

instance (HasTrie a, Ord b) => Ord (a :->: b) where
  compare = compare `on` toList

instance (HasTrie a, Show a, Show b) => Show (a :->: b) where 
  showsPrec d = showsPrec d . toKeyedList

instance HasTrie a => Apply ((:->:) a) where
  (<.>) = apRep
  a <. _ = a
  _ .> b = b

instance HasTrie a => Applicative ((:->:) a) where
  pure a = Trie (pureRep a)
  (<*>) = apRep
  a <* _ = a
  _ *> b = b

instance HasTrie a => Bind ((:->:) a) where
  Trie m >>- f = Trie (tabulate (\a -> index (runTrie (f (index m a))) a))
  
instance HasTrie a => Monad ((:->:) a) where
  return a = Trie (pureRep a)
  (>>=) = (>>-)
  _ >> m = m

instance HasTrie a => MonadReader a ((:->:) a) where
  ask = askRep
  local = localRep

-- TODO: remove dependency on HasTrie in these: 

instance (HasTrie m, Semigroup m, Monoid m) => Comonad ((:->:) m) where
  extract = flip index mempty


instance (HasTrie m, Semigroup m) => Extend ((:->:) m) where
  duplicate = duplicateRep

-- * Instances

instance HasTrie () where
  type BaseTrie () = Identity
  embedKey = id
  projectKey = id

instance HasTrie Bool where
  type BaseTrie Bool = BoolTrie
  embedKey = id
  projectKey = id

instance HasTrie Any where
  type BaseTrie Any = BoolTrie
  embedKey = getAny
  projectKey = Any

instance HasTrie a => HasTrie (Dual a) where
  type BaseTrie (Dual a) = BaseTrie a
  embedKey = embedKey . getDual
  projectKey = Dual . projectKey 

instance HasTrie a => HasTrie (Sum a) where
  type BaseTrie (Sum a) = BaseTrie a
  embedKey = embedKey . getSum
  projectKey = Sum . projectKey 

instance HasTrie a => HasTrie (Monoid.Product a) where
  type BaseTrie (Monoid.Product a) = BaseTrie a
  embedKey = embedKey . Monoid.getProduct
  projectKey = Monoid.Product . projectKey 

instance (HasTrie a, HasTrie b) => HasTrie (a, b) where
  type BaseTrie (a, b) = ReaderT (BaseTrie a) (BaseTrie b)
  embedKey = embedKey *** embedKey
  projectKey = projectKey *** projectKey

instance (HasTrie a, HasTrie b) => HasTrie (Entry a b) where
  type BaseTrie (Entry a b) = ReaderT (BaseTrie a) (BaseTrie b)
  embedKey (Entry a b) = (embedKey a, embedKey b)
  projectKey (a, b) = Entry (projectKey a) (projectKey b)

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type BaseTrie (Either a b) = EitherTrie (BaseTrie a) (BaseTrie b)
  embedKey = embedKey +++ embedKey
  projectKey = projectKey +++ projectKey

instance HasTrie a => HasTrie (Maybe a) where
  type BaseTrie (Maybe a) = EitherTrie Identity (BaseTrie a)
  embedKey   = maybe (Left ()) (Right . embedKey)
  projectKey = either (const Nothing) (Just . projectKey)

instance HasTrie a => HasTrie [a] where
  type BaseTrie [a] = ListTrie (BaseTrie a)
  embedKey = map embedKey
  projectKey = map projectKey

instance HasTrie a => HasTrie (Seq a) where
  type BaseTrie (Seq a) = ListTrie (BaseTrie a)
  embedKey = foldr ((:) . embedKey) []
  projectKey = foldr ((<|) . projectKey) (Seq.empty)

instance (HasTrie k, HasTrie v) => HasTrie (Map k v) where
  type BaseTrie (Map k v) = ListTrie (BaseTrie (k, v))
  embedKey = foldrWithKey (\k v t -> embedKey (k,v) : t) []
  projectKey = Map.fromDistinctAscList . map projectKey

instance (HasTrie v) => HasTrie (IntMap v) where
  type BaseTrie (IntMap v) = ListTrie (BaseTrie (Int, v))
  embedKey = foldrWithKey (\k v t -> embedKey (k,v) : t) []
  projectKey = IntMap.fromDistinctAscList . map projectKey

  
-- | Extract bits in little-endian order
bits :: Bits t => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)

-- | Convert boolean to 0 (False) or 1 (True)
unbit :: Num t => Bool -> t
unbit False = 0
unbit True  = 1

-- | Bit list to value
unbits :: Bits t => [Bool] -> t
unbits [] = 0
unbits (x:xs) = unbit x .|. shiftL (unbits xs) 1

unbitsZ :: (Bits n) => (Bool,[Bool]) -> n
unbitsZ (positive,bs) = sig (unbits bs)
 where
   sig | positive  = id
       | otherwise = negate

bitsZ :: (Ord n, Bits n) => n -> (Bool,[Bool])
bitsZ = (>= 0) &&& (bits . abs)

-- TODO: fix the show instance of this
instance HasTrie Int where
  type BaseTrie Int = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

instance HasTrie Int8 where
  type BaseTrie Int8 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

instance HasTrie Int16 where
  type BaseTrie Int16 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

instance HasTrie Int32 where
  type BaseTrie Int32 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

instance HasTrie Int64 where
  type BaseTrie Int64 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

instance HasTrie Word where
  type BaseTrie Word = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey
instance HasTrie Word8 where
  type BaseTrie Word8 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey
instance HasTrie Word16 where
  type BaseTrie Word16 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey
instance HasTrie Word32 where
  type BaseTrie Word32 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey
instance HasTrie Word64 where
  type BaseTrie Word64 = BaseTrie (Bool, [Bool])
  embedKey = embedKey . bitsZ 
  projectKey = unbitsZ . projectKey

-- TODO: fix tree to 21 bit depth
instance HasTrie Char where
  type BaseTrie Char = BaseTrie [Bool]
  embedKey = bits . fromEnum
  projectKey = toEnum . unbits

instance (HasTrie a, HasTrie b, HasTrie c) => HasTrie (a,b,c) where
  type BaseTrie (a,b,c) = BaseTrie (a,(b,c))
  embedKey (a,b,c) = embedKey (a,(b,c))
  projectKey p = let (a,(b,c)) = projectKey p in (a,b,c)

instance (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => HasTrie (a,b,c,d) where
  type BaseTrie (a,b,c,d) = BaseTrie ((a,b),(c,d))
  embedKey (a,b,c,d) = embedKey ((a,b),(c,d))
  projectKey p = let ((a,b),(c,d)) = projectKey p in (a,b,c,d)
