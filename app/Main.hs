{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Main where

import GHC.Generics qualified as G
import GHC.TypeLits
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad.State hiding (lift)
import Control.Monad.Identity
import Data.Monoid (First(..))
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Fix (Fix(..))
import Text.Show.Deriving
import Control.Lens qualified as L

main :: IO ()
main = putStrLn "Hello, Haskell!"

instance Lift Bytes where
    lift _ = error "Cannot lift Bytes."
    liftTyped _ = error "Cannot lift Bytes."

deriving instance Lift AnnTarget
deriving instance Lift RuleBndr
deriving instance Lift InjectivityAnn
deriving instance Lift Phases
deriving instance Lift FamilyResultSig
deriving instance Lift RuleMatch
deriving instance Lift Inline
deriving instance Lift FixityDirection
deriving instance Lift Safety
deriving instance Lift Callconv
deriving instance Lift SourceStrictness
deriving instance Lift SourceUnpackedness
deriving instance Lift PkgName
deriving instance Lift NameSpace
deriving instance Lift PatSynDir
deriving instance Lift PatSynArgs
deriving instance Lift DerivStrategy
deriving instance Lift Role
deriving instance Lift TypeFamilyHead
deriving instance Lift TySynEqn
deriving instance Lift Pragma
deriving instance Lift Fixity
deriving instance Lift Foreign
deriving instance Lift Overlap
deriving instance Lift FunDep
deriving instance Lift Bang
deriving instance Lift ModName
deriving instance Lift DerivClause
deriving instance Lift Con
deriving instance Lift Clause
deriving instance Lift Body
deriving instance Lift TyLit
deriving instance Lift TyVarBndr
deriving instance Lift NameFlavour
deriving instance Lift OccName
deriving instance Lift Range
deriving instance Lift Stmt
deriving instance Lift Dec
deriving instance Lift Guard
deriving instance Lift Match
deriving instance Lift Pat
deriving instance Lift Type
deriving instance Lift Lit
deriving instance Lift Name
deriving instance Lift Exp
deriving instance Lift Info

-- Nth constructors
class NthConstructor t where
  constructorToN :: t -> Int
  default constructorToN :: (G.Generic t, GNthConstructor (G.Rep t)) => t -> Int
  constructorToN = gConstructorToN . G.from

class NthConstructor1 f where
  constructorToN1 :: f a -> Int
  default constructorToN1 :: (G.Generic1 f, GNthConstructor (G.Rep1 f)) => f a -> Int
  constructorToN1 = gConstructorToN . G.from1

class GNthConstructor f where
  gConstructorToN :: f a -> Int

instance (KnownNat (Size f), GNthConstructor f, GNthConstructor g) => GNthConstructor (f G.:+: g) where
  gConstructorToN (G.L1 f) = gConstructorToN f
  gConstructorToN (G.R1 g) = size (Proxy @f) + gConstructorToN g

instance GNthConstructor (G.C1 meta g) where
  gConstructorToN _ = 0

instance GNthConstructor g => GNthConstructor (G.D1 meta g) where
  gConstructorToN = gConstructorToN . G.unM1

type family Size (rep :: k) :: Nat

type instance Size (G.D1 meta f) = Size f
type instance Size (G.C1 meta g) = 1
type instance Size (f G.:+: g) = Size f + Size g

size :: forall f n a. (KnownNat n, Size f ~ n) => Proxy f -> Int
size _ = fromIntegral $ natVal (Proxy @n)

class NthConstructorName f where
  nthConstructorName :: Proxy f -> Int -> String
  default nthConstructorName :: (G.Generic1 f, GNthConstructorName (G.Rep1 f)) => Proxy f -> Int -> String
  nthConstructorName proxy = gNthConstructorName (Proxy @(G.Rep1 f))

class GNthConstructorName f where
  gNthConstructorName :: Proxy f -> Int -> String

instance GNthConstructorName g => GNthConstructorName (G.D1 meta g) where
  gNthConstructorName proxy i = gNthConstructorName (Proxy @g) i

instance KnownSymbol name => GNthConstructorName (G.C1 (G.MetaCons name fixity bool) g) where
  gNthConstructorName _ 0 = symbolVal (Proxy @name)
  gNthConstructorName _ n = error $ "Tried to get gNthConstructorName for C1 with nonzero index " ++ show n

instance (KnownNat (Size f), GNthConstructorName f, GNthConstructorName g) => GNthConstructorName (f G.:+: g) where
  gNthConstructorName _ i =
    let leftSize = size (Proxy @f)
    in
    if i < leftSize
       then gNthConstructorName (Proxy @f) i
       else gNthConstructorName (Proxy @g) (i - leftSize)

data Proxy n = Proxy

-- Use keys
makeBaseFunctor ''Exp
deriving instance Show a => Show (ExpF a)
deriving instance Eq a => Eq (ExpF a)
deriving instance Ord a => Ord (ExpF a)
deriving instance G.Generic a => G.Generic (ExpF a)
deriving instance G.Generic1 ExpF
deriveShow1 ''ExpF
instance NthConstructor1 ExpF
instance NthConstructorName ExpF

data X a = A a | B Char | C Int Int
  deriving (Show, Eq, Ord, G.Generic, G.Generic1, Functor, Foldable, Traversable)

instance NthConstructor (X a)
instance NthConstructor1 X

data LC
  = Lit Integer
  | Var String
  | App LC LC
  | Abs String LC
  deriving (Show, Eq, Ord, G.Generic)

data Key t = Key { constructor :: Int, field :: Int }
  deriving (Show, Eq, Ord, G.Generic)

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

modifyKey :: (NthConstructor1 f, Traversable f) => Key f -> (a -> a) -> f a -> f a
modifyKey = L.over . traversalKey

getKey :: (NthConstructor1 f, Traversable f) => Key f -> f a -> Maybe a
getKey = L.preview . traversalKey

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

modifyDeepKey
  :: forall t f
   . (Base t ~ f, Corecursive t, Recursive t, NthConstructor1 f, Traversable f)
  => DeepKey f -> (t -> t) -> t -> t
modifyDeepKey = L.over . traversalDeepKey

getDeepKey
  :: forall t f
   . (Base t ~ f, Corecursive t, Recursive t, NthConstructor1 f, Traversable f)
  => DeepKey f -> t -> Maybe t
getDeepKey = L.preview . traversalDeepKey

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
