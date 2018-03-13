 
module Test.Laws.Ord 
  ( law_Ord_reflexive
  , law_Ord_transitive
  , law_Ord_antisymmetric
  , law_Ord_total
  , checkOrd
  ) where

import Data.Proxy
import Data.Typeable

import Test.QuickCheck

import Test.Utilities
import Test.Laws.Eq ( checkEq )

-- Laws for ordering relationships...
law_Ord_reflexive :: (Ord a) => Proxy a -> a -> Bool
law_Ord_reflexive _ a = a <= a

law_Ord_transitive :: (Ord a) => Proxy a -> a -> a -> a -> Property
law_Ord_transitive _ a b c = (a <= b) && (b <= c) ==> (a <= c)

law_Ord_antisymmetric :: (Ord a) => Proxy a -> a -> a -> Property
law_Ord_antisymmetric _ a b = (a <= b) && (b <= a) ==> a == b

law_Ord_total :: (Ord a) => Proxy a -> a -> a -> Bool
law_Ord_total _ a b = (a <= b) || (b <= a)

checkOrd :: (Arbitrary a, Typeable a, Show a, Ord a) => Int -> Proxy a -> IO Result
checkOrd n p = checkEq n p
          &&&& check n p "Ord.Reflexive" law_Ord_reflexive
          &&&& check n p "Ord.Antisymmetric" law_Ord_antisymmetric
          &&&& check n p "Ord.Transitive" law_Ord_transitive
          &&&& check n p "Ord.Total" law_Ord_total