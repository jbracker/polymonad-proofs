 
module Test.Laws.Endo.Functor 
  ( law_Endo_Functor_id
  , law_Endo_Functor_compose
  , law_Endo_CoFunctor_id
  , law_Endo_CoFunctor_compose
  , checkEndoFunctor
  ) where

import Prelude hiding ( map )

import Data.Proxy ( Proxy(..) )
import Data.Typeable

import Test.Types.Endo

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.Utilities

law_Endo_Functor_id :: (Eq a) => Proxy a -> Endo a -> a -> Bool
law_Endo_Functor_id _ = map id `endo_fun_eq` id

law_Endo_Functor_compose :: (Eq a) => Proxy a -> Fun a a -> Fun a a -> (Endo a -> a -> Bool)
law_Endo_Functor_compose _ f' g' = map (f . g) `endo_fun_eq` (map f . map g)
  where f = apply f'
        g = apply g'

law_Endo_CoFunctor_id :: (Eq a) => Proxy a -> Endo a -> a -> Bool
law_Endo_CoFunctor_id _ = comap id `endo_fun_eq` id

law_Endo_CoFunctor_compose :: (Eq a) => Proxy a -> Fun a a -> Fun a a -> (Endo a -> a -> Bool)
law_Endo_CoFunctor_compose _ f' g' = comap (f . g) `endo_fun_eq` (comap g . comap f)
  where f = apply f'
        g = apply g'

checkEndoFunctor :: ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a, Eq a) 
                 => Int -> Proxy a -> IO Result
checkEndoFunctor n p = check n p "Endo.Functor.Id"      law_Endo_Functor_id
                  &&&& check n p "Endo.Functor.Compose" law_Endo_Functor_compose
                  &&&& check n p "Endo.CoFunctor.Id"      law_Endo_CoFunctor_id
                  &&&& check n p "Endo.CoFunctor.Compose" law_Endo_CoFunctor_compose