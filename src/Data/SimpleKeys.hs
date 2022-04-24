{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Data.SimpleKeys where

import GHC.Generics qualified as G
import GHC.TypeLits
import Control.Monad.State hiding (lift)
import Control.Monad.Identity
import Data.Monoid (First(..))
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Fix (Fix(..))

-- Nth constructors
class NthConstructor t where
  constructorToN :: t -> Int
  default constructorToN
    :: forall rep
     . (G.Generic t, rep ~ G.Rep t, GNthConstructor rep, SumsToBinTree rep)
    => t -> Int
  constructorToN t = gConstructorToN (G.from t) (sumsToBinTree (Proxy @(G.Rep t)))

class NthConstructor1 f where
  constructorToN1 :: f a -> Int
  default constructorToN1
    :: forall rep a
     . (G.Generic1 f, rep ~ G.Rep1 f, GNthConstructor rep, SumsToBinTree rep)
    => f a -> Int
  constructorToN1 fa = gConstructorToN (G.from1 fa) (sumsToBinTree (Proxy @rep))

class GNthConstructor f where
  gConstructorToN :: f a -> SizedBinTree -> Int

instance (GNthConstructor f, GNthConstructor g) => GNthConstructor (f G.:+: g) where
  gConstructorToN (G.L1 f) (Node _ l r) = gConstructorToN f l
  gConstructorToN (G.R1 g) (Node _ l r) = sizeBT l + gConstructorToN g r
  gConstructorToN _ _ = error "gConstructorToN: binary tree mismatch"

instance GNthConstructor (G.C1 meta g) where
  gConstructorToN _ _ = 0

instance GNthConstructor g => GNthConstructor (G.D1 meta g) where
  gConstructorToN = gConstructorToN . G.unM1

data SizedBinTree = Node Int SizedBinTree SizedBinTree | Leaf
  deriving (Show, Eq, Ord)

sizeBT :: SizedBinTree -> Int
sizeBT Leaf = 1
sizeBT (Node size _ _) = size

mkNode :: SizedBinTree -> SizedBinTree -> SizedBinTree
mkNode l r = Node (sizeBT l + sizeBT r) l r

class SumsToBinTree f where
  sumsToBinTree :: Proxy f -> SizedBinTree

instance SumsToBinTree f => SumsToBinTree (G.D1 meta f) where
  sumsToBinTree _ = sumsToBinTree (Proxy @f)

instance (SumsToBinTree f, SumsToBinTree g) => SumsToBinTree (f G.:+: g) where
  sumsToBinTree _ = mkNode (sumsToBinTree (Proxy @f)) (sumsToBinTree (Proxy @g))

instance SumsToBinTree (G.C1 meta f) where
  sumsToBinTree _ = Leaf

class NthConstructorName f where
  nthConstructorName :: Proxy f -> Int -> String
  default nthConstructorName
    :: forall rep
     . (G.Generic1 f, rep ~ G.Rep1 f, GNthConstructorName rep, SumsToBinTree rep)
    => Proxy f -> Int -> String
  nthConstructorName proxy =
    let proxy = Proxy @rep
     in gNthConstructorName proxy (sumsToBinTree proxy)

class GNthConstructorName f where
  gNthConstructorName :: Proxy f -> SizedBinTree -> Int -> String

instance GNthConstructorName g => GNthConstructorName (G.D1 meta g) where
  gNthConstructorName proxy = gNthConstructorName (Proxy @g)

instance KnownSymbol name => GNthConstructorName (G.C1 (G.MetaCons name fixity bool) g) where
  gNthConstructorName _ _ 0 = symbolVal (Proxy @name)
  gNthConstructorName _ _ n = error $ "Tried to get gNthConstructorName for C1 with nonzero index " ++ show n

instance (GNthConstructorName f, GNthConstructorName g) => GNthConstructorName (f G.:+: g) where
  gNthConstructorName _ (Node _ l r) i =
    let leftSize = sizeBT l
    in
    if i < leftSize
       then gNthConstructorName (Proxy @f) l i
       else gNthConstructorName (Proxy @g) r (i - leftSize)

data Proxy n = Proxy

data Key t = Key { constructor :: Int, field :: Int }
  deriving (Show, Eq, Ord)

newtype Debug t = Debug { unDebug :: t }

instance NthConstructorName t => Show (Debug (Key t)) where
  show (Debug Key { constructor, field }) =
    concat
      [ "Key { "
      , nthConstructorName (Proxy @t) constructor
      , " (", show constructor, "), "
      , show field
      , "}"
      ]

instance Show (Debug t) => Show (Debug [t]) where
  show (Debug keys) = show $ map Debug keys

traversalKey
  :: forall f m a
   . (NthConstructor1 f, Traversable f, Applicative m)
  => Key f -> (a -> m a) -> f a -> m (f a)
traversalKey Key { constructor, field } handler datatype
  | constructorToN1 datatype == constructor
  = let go :: a -> State Int (m a)
        go a = do
          n <- get
          modify succ
          pure $ if n == field then handler a else pure a
    in
    sequenceA $ evalState (traverse go datatype) 0

annKey
  :: forall f a
   . (NthConstructor1 f, Traversable f)
  => f a -> f (Key f, a)
annKey datatype = evalState (traverse go datatype) 0
  where
    go :: a -> State Int (Key f, a)
    go a = do
      field <- get
      modify succ
      let key = Key (constructorToN1 datatype) field
      pure (key, a)

type DeepKey f = [Key f]
type AnnF ann f = Product (Const ann) f
type Ann ann f = Fix (AnnF ann f)

traversalDeepKey
  :: forall t f m a
   . (Base t ~ f, Applicative m, Corecursive t, Recursive t, NthConstructor1 f, Traversable f)
  => DeepKey f -> (t -> m t) -> t -> m t
traversalDeepKey [] handler = handler
traversalDeepKey (key:rest) handler =
  fmap embed . traversalKey key (traversalDeepKey rest handler) . project

annKeyDeep
  :: forall t base
   . (Recursive t, base ~ Base t, NthConstructor1 base, Traversable base)
  => t -> Ann (DeepKey base) base
annKeyDeep t = overAnn reverse $ cata go t []
  where
    go :: base (DeepKey base -> Ann (DeepKey base) base)
             -> DeepKey base -> Ann (DeepKey base) base
    go base keys = Fix (Pair (Const keys) (fmap passKeys $ annKey base))
      where
        passKeys (keyHead, cont) = cont (keyHead : keys)

overAnn
  :: forall base ann ann'
   . Functor base
  => (ann -> ann')
  -> Ann ann base -> Ann ann' base
overAnn editAnn = hoist $ \(Pair (Const ann) f) -> Pair (Const (editAnn ann)) f
