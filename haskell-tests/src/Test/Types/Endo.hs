
{-# LANGUAGE TypeFamilies #-}

-- Yes, we have an orphan in here, don't make a fuss...
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Types.Endo 
  ( Endo(..)
  , map, comap
  , ap, pure
  
    -- * Approximate equalities for endomorphisms
  , endo_eq
  , endo_eq'
  , endo_fun_eq
  ) where

import Prelude hiding ( map, pure )

import Data.Monoid ( Endo(..) )

import Test.Schemes
import Test.Equality

import Test.QuickCheck.Function

-- | The functor mapping for endomorphisms
map :: (a ~ b) => Fmap Endo a b
map f (Endo g) = Endo $ f . g

-- | The cofunctor mapping for endomorphisms.
comap :: (a ~ b) => Fmap Endo b a
comap f (Endo g) = Endo $ g . f

-- | Applicative @<*>@ for endofunctors.
ap :: (a ~ b) => Ap Endo a b
ap (Endo ff) (Endo fa) = Endo $ ff fa

-- | @pure@ for endofunctors.
pure :: Pure Endo a
pure _ = Endo id


-- | Show an approximation of the given endomorphism.
instance (Function a, Show a) => Show (Endo a) where
  show e = show $ function $ appEndo e


-- | Approximate equality of endomorphisms using functions extensionality
endo_eq :: (Eq a) => Endo a -> Endo a -> a -> Bool
endo_eq (Endo f) (Endo g) a = funext_eq1 f g a

-- | Approximate equality of endomorphisms using functions extensionality
endo_eq' :: (Eq b) => Endo (a -> b) -> Endo (a -> b) -> ((a -> b) -> a -> Bool)
endo_eq' (Endo f) (Endo g) h a = funext_eq2 f g h a

-- | Approximate equality of functions over endomorphisms using functions extensionality
endo_fun_eq :: (Eq b) => (Endo a -> Endo b) -> (Endo a -> Endo b) -> Endo a -> b -> Bool
endo_fun_eq f g e = f e `endo_eq` g e

infixl 4 `ap`
infixl 4 `endo_eq`
infixl 4 `endo_eq'`
infixl 4 `endo_fun_eq`