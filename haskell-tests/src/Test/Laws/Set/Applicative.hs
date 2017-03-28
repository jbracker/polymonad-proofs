
{-# LANGUAGE TupleSections #-}

-- | The laws stated here for set are the ones for the monoidal version,
--   because the standard versions involves 'Set's of functions which
--   does not make a lot of sense in Haskell.
module Test.Laws.Set.Applicative 
  ( law_Set_Applicative_naturality
  , law_Set_Applicative_left_identity
  , law_Set_Applicative_right_identity
  , law_Set_Applicative_assoc
  ) where

import Prelude hiding ( map, pure, (**) )

import Data.Set
import Data.Proxy

import Control.Arrow ( (***) )

import Test.QuickCheck.Function

import Test.Types.Set

law_Set_Applicative_naturality :: (Ord a, Ord b, Ord c, Ord d) 
                               => Proxy (a, b) -> Proxy (c, d) -> Fun a b -> Fun c d -> Set a -> Set c -> Bool
law_Set_Applicative_naturality _ _ f' g' u v = map (f *** g) (u ** v) == map f u ** map g v
  where f = apply f'
        g = apply g'

law_Set_Applicative_left_identity :: (Ord a) => Proxy a -> Set a -> Bool
law_Set_Applicative_left_identity _ s = unit ** s == map ((),) s

law_Set_Applicative_right_identity :: (Ord a) => Proxy a -> Set a -> Bool
law_Set_Applicative_right_identity _ s = s ** unit == map (,()) s

law_Set_Applicative_assoc :: (Ord a, Ord b, Ord c) => Proxy (a,b,c) -> Set a -> Set b -> Set c -> Bool
law_Set_Applicative_assoc _ s t r = s ** (t ** r) == map (\((a,b),c)->(a,(b,c))) ((s ** t) ** r)