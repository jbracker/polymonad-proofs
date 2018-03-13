
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

module Test.Laws.Set.Functor 
  ( law_Set_Functor_compose
  , law_Set_Functor_id
  , checkSetFunctor
  ) where

import Prelude hiding ( map )

import Data.Set
import Data.Proxy ( Proxy(..) )
import Data.Typeable

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.Utilities

-- | Functor compose law for 'Set'.
law_Set_Functor_compose :: (Ord b, Ord c) => Proxy (a, b, c) -> Set a -> Fun a b -> Fun b c -> Bool
law_Set_Functor_compose _ s f' g' = map (g . f) s == (map g . map f) s
  where f = apply f'
        g = apply g'

-- | Functor identity law for 'Set'.
law_Set_Functor_id :: (Ord a) => Proxy a -> Set a -> Bool
law_Set_Functor_id _ s = map id s == s


checkSetFunctor :: forall a b c.
  ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a, Ord a
  , Function b, CoArbitrary b, Arbitrary b, Typeable b, Show b, Ord b
  , Function c, CoArbitrary c, Arbitrary c, Typeable c, Show c, Ord c
  ) => Int -> Proxy (a,b,c) -> IO Result
checkSetFunctor n p = check n (Proxy :: Proxy a) "FunctorSet.Id" law_Set_Functor_id 
                 &&&& check n (Proxy :: Proxy b) "FunctorSet.Id" law_Set_Functor_id 
                 &&&& check n (Proxy :: Proxy c) "FunctorSet.Id" law_Set_Functor_id 
                 &&&& checkAll3 (Proxy :: Proxy Ord) p (checkCompose n)
  where
    checkCompose m q = check m q "FunctorSet.Compose" law_Set_Functor_compose
