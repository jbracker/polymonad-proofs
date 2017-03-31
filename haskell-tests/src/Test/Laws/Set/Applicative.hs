
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The laws stated here for set are the ones for the monoidal version,
--   because the standard versions involves 'Set's of functions which
--   does not make a lot of sense in Haskell.
module Test.Laws.Set.Applicative 
  ( law_Set_Applicative_naturality
  , law_Set_Applicative_left_identity
  , law_Set_Applicative_right_identity
  , law_Set_Applicative_associativity
  , checkSetApplicative
  ) where

import Prelude hiding ( map, pure, (**) )

import Data.Set
import Data.Proxy
import Data.Typeable

import Control.Arrow ( (***) )

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.Types.Set
import Test.Utilities

law_Set_Applicative_naturality :: (Ord a, Ord b, Ord c, Ord d) 
                               => Proxy (a, b) -> Proxy (c, d) -> Fun a b -> Fun c d -> Set a -> Set c -> Bool
law_Set_Applicative_naturality _ _ f' g' u v = map (f *** g) (u ** v) == map f u ** map g v
  where f = apply f'
        g = apply g'

law_Set_Applicative_left_identity :: (Ord a) => Proxy a -> Set a -> Bool
law_Set_Applicative_left_identity _ s = unit ** s == map ((),) s

law_Set_Applicative_right_identity :: (Ord a) => Proxy a -> Set a -> Bool
law_Set_Applicative_right_identity _ s = s ** unit == map (,()) s

law_Set_Applicative_associativity :: (Ord a, Ord b, Ord c) => Proxy (a,b,c) -> Set a -> Set b -> Set c -> Bool
law_Set_Applicative_associativity _ s t r = s ** (t ** r) == map (\((a,b),c)->(a,(b,c))) ((s ** t) ** r)

checkSetApplicative :: forall a b c d.
  ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a, Ord a
  , Function b, CoArbitrary b, Arbitrary b, Typeable b, Show b, Ord b
  , Function c, CoArbitrary c, Arbitrary c, Typeable c, Show c, Ord c
  , Function d, CoArbitrary d, Arbitrary d, Typeable d, Show d, Ord d
  ) => Int -> Proxy (a,b,c,d) -> IO Result
checkSetApplicative n _ 
     = check n (Proxy :: Proxy a) "ApplicativeSet.LeftIdentity" law_Set_Applicative_left_identity 
  &&&& check n (Proxy :: Proxy b) "ApplicativeSet.LeftIdentity" law_Set_Applicative_left_identity 
  &&&& check n (Proxy :: Proxy c) "ApplicativeSet.LeftIdentity" law_Set_Applicative_left_identity 
  &&&& check n (Proxy :: Proxy d) "ApplicativeSet.LeftIdentity" law_Set_Applicative_left_identity
  
  &&&& check n (Proxy :: Proxy a) "ApplicativeSet.RightIdentity" law_Set_Applicative_right_identity 
  &&&& check n (Proxy :: Proxy b) "ApplicativeSet.RightIdentity" law_Set_Applicative_right_identity 
  &&&& check n (Proxy :: Proxy c) "ApplicativeSet.RightIdentity" law_Set_Applicative_right_identity 
  &&&& check n (Proxy :: Proxy d) "ApplicativeSet.RightIdentity" law_Set_Applicative_right_identity 
  
  &&&& checkAll3 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,b,c)) (checkAssoc n)
  &&&& checkAll3 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,b,d)) (checkAssoc n)
  &&&& checkAll3 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,c,d)) (checkAssoc n)
  &&&& checkAll3 (Proxy :: Proxy Ord) (Proxy :: Proxy (b,c,d)) (checkAssoc n)
  
  &&&& checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,b)) (\p' -> checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (c,d)) (checkNatural n p'))
  &&&& checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (c,d)) (\p' -> checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,b)) (checkNatural n p'))
  &&&& checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (a,c)) (\p' -> checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (b,d)) (checkNatural n p'))
  &&&& checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (d,b)) (\p' -> checkAll2 (Proxy :: Proxy Ord) (Proxy :: Proxy (c,a)) (checkNatural n p'))
  where
    checkNatural m q q' = check m q' "ApplicativeSet.Naturality" (law_Set_Applicative_naturality q)
    checkAssoc m q = check m q "ApplicativeSet.Associativity" law_Set_Applicative_associativity
    