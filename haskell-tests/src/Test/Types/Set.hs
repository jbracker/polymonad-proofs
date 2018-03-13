
{-# LANGUAGE FlexibleContexts #-}

module Test.Types.Set
  ( tensor, (**)
  , unit
  , map
  , pure
  , ap
  ) where

import Prelude hiding ( map, pure, (**) )

import Data.Set

-- | Monoidal tensor product for sets.
tensor :: (Ord a, Ord b) => Set a -> Set b -> Set (a , b)
tensor sa sb = fold (\a s -> s `union` map (\b -> (a , b)) sb) empty sa

-- | Operator for the tensor product.
(**) :: (Ord a, Ord b) => Set a -> Set b -> Set (a , b)
(**) = tensor

-- | Monoidal unit of the sensor for sets.
unit :: Set ()
unit = singleton ()

-- | We can define 'ap' in terms for 'tensor' but it does not make a 
--   lot of sense to ever use it, since we don't have an ordering for functions.
ap :: (Ord (a -> b), Ord a, Ord b) => Set (a -> b) -> Set a -> Set b
ap sf sa = map (uncurry ($)) (sf ** sa)

-- | Pure defined in terms of monoidal 'unit' and 'map'.
pure :: (Ord a) => a -> Set a
pure a = map (const a) unit