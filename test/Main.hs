{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Main where

import GHC.Generics qualified as G
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Text.Show.Deriving

import Data.SimpleKeys
import LiftTH

main :: IO ()
main = pure ()

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

x = $(lift =<< [| 3 + 4 |])
y = $(lift =<< [| 3 * 4 + 5 * 6 |])
z = $(lift =<< [| f 1 2 3 4 5 |])

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
