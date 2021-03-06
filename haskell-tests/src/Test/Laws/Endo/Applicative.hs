
-- | ...
module Test.Laws.Endo.Applicative
  ( law_Endo_Applicative_identity
  , law_Endo_Applicative_homomorphism
  , checkFailEndoApplicative
  ) where

import Prelude hiding ( pure, map, (**) )

import Data.Proxy
import Data.Typeable

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.Types.Endo
import Test.Utilities

law_Endo_Applicative_identity :: (Eq a) => Proxy a -> Endo a -> (a -> Bool)
law_Endo_Applicative_identity _ v = (pure id `ap` v) `endo_eq` v

{- 
-- Does not work:
--   endo_pure (.) :: Endo ((b -> c) -> (a -> b) -> (a -> c))
-- but the first 'endo_ap' requires something of the form 'Endo (a -> a)'
-- which does not unify with the above type.
law_Endo_Applicative_composition :: (Eq c) => Endo (b -> c) -> Endo (a -> c) -> Endo a -> (a -> c) -> a -> Bool
law_Endo_Applicative_composition u v w = (endo_pure (.) `endo_ap` u `endo_ap` v `endo_ap` w) `endo_fun_eq` (u `endo_ap` (v `endo_ap` w))
-}

law_Endo_Applicative_homomorphism :: (Eq a) => Proxy a -> Fun a a -> a -> (a -> Bool)
law_Endo_Applicative_homomorphism _ f' x = (pure f `ap` pure x) `endo_eq` (pure (f x))
  where f = apply f'

{-
-- Does not work for the same reason:
--   endo_pure ($ y) :: Endo ((a -> b) -> b)
-- but 'endo_ap' requires something of the form 'Endo (a -> a)' so this law does not typecheck.
law_Endo_Applicative_interchange :: (Eq a) => Endo (a -> a) -> a -> a -> Bool
law_Endo_Applicative_interchange u y = (u `endo_ap` endo_pure y) `endo_eq` (endo_pure ($ y) `endo_ap` u)
-}

checkFailEndoApplicative ::
  ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a, Eq a
  ) => Int -> Proxy a -> IO Result
checkFailEndoApplicative n p 
     = check n p "NOT FunctorEndo.Id" (\q -> expectFailure $ law_Endo_Applicative_identity q)
  &&&& check n p "NOT FunctorEndo.Id" (\q -> expectFailure $ law_Endo_Applicative_homomorphism q) 