 
module Test.Laws.Eq 
  ( law_Eq_reflexive
  , law_Eq_symmetric
  , law_Eq_transitive
  , checkEq
  ) where

import Data.Proxy
import Data.Typeable

import Test.Utilities

import Test.QuickCheck

-- Laws for equivalence relationships...
law_Eq_reflexive :: (Eq a) => Proxy a -> a -> Bool
law_Eq_reflexive _ a = a == a

law_Eq_symmetric :: (Eq a) => Proxy a -> a -> a -> Property
law_Eq_symmetric _ a b = (a == b) ==> (b == a)

law_Eq_transitive :: (Eq a) => Proxy a -> a -> a -> a -> Property
law_Eq_transitive _ a b c = (a == b) && (b == c) ==> (a == c)

checkEq :: (Arbitrary a, Typeable a, Show a, Eq a) => Int -> Proxy a -> IO Result
checkEq n p = check n p "Eq.Reflexive"  law_Eq_reflexive
         &&&& check n p "Eq.Symmetric"  law_Eq_symmetric
         &&&& check n p "Eq.Transitive" law_Eq_transitive