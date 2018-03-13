
-- | For the 'CoArbitrary' and 'Function' instances we have to make sure that 
--   the functions are actually congruent, because otherwise the laws can be 
--   broken by them. This happens because the functions are able to cheat by
--   differentiating values by their internal representation although they
--   are logically the same value, but equal objects should never deliver 
--   different results for a proper quotient type.
--   
--   To test this behaviour this module also offers 'NonCongruentIntMod2' 
--   which breaks the abstractness of the quotient type and has generators
--   that create non-congruent functions on purpose.
module Test.Types 
  ( -- * Congruent quotient types
    IntMod2 , unIntMod2
  , IntMod3 , unIntMod3
    -- * Non-congruent quotient types
  , NonCongruentIntMod2(..) ) where

import Data.Typeable

import Test.QuickCheck
import Test.QuickCheck.Function

-- -----------------------------------------------------------------------------
-- Congruent quotient types
-- -----------------------------------------------------------------------------

-- | Integer quotient type that has different representations for the same 
--   value internally.
newtype IntMod2 = IntMod2 Int deriving ( Typeable )

-- | Integer quotient type that has different representations for the same 
--   value internally.
newtype IntMod3 = IntMod3 Int deriving ( Typeable )

-- | Normalises representation when unpacking, therefore there is no way 
--   to distinguish different internal representations.
unIntMod2 :: IntMod2 -> Int
unIntMod2 (IntMod2 n) = mod n 2

-- | Normalises representation when unpacking, therefore there is no way 
--   to distinguish different internal representations.
unIntMod3 :: IntMod3 -> Int
unIntMod3 (IntMod3 n) = mod n 3

instance Eq IntMod2 where
  n == m = unIntMod2 n == unIntMod2 m
instance Eq IntMod3 where
  n == m = unIntMod3 n == unIntMod3 m

instance Ord IntMod2 where
  compare n m = compare (unIntMod2 n) (unIntMod2 m)
instance Ord IntMod3 where
  compare n m = compare (unIntMod3 n) (unIntMod3 m)

-- | This instance does not normalize and therefore actually 
--   generates different internal representations.
instance Arbitrary IntMod2 where
  arbitrary = IntMod2 . abs <$> arbitrary
-- | This instance does not normalize and therefore actually 
--   generates different internal representations.
instance Arbitrary IntMod3 where
  arbitrary = IntMod3 . abs <$> arbitrary
  
instance Show IntMod2 where
  show n = show (unIntMod2 n) ++ "%2"
instance Show IntMod3 where
  show n = show (unIntMod3 n) ++ "%3"

instance CoArbitrary IntMod2 where
  coarbitrary n = coarbitrary (unIntMod2 n)
instance CoArbitrary IntMod3 where
  coarbitrary n = coarbitrary (unIntMod3 n)

instance Function IntMod2 where
  function f = functionMap unIntMod2 IntMod2 f
instance Function IntMod3 where
  function f = functionMap unIntMod3 IntMod3 f

-- -----------------------------------------------------------------------------
-- Non-congruent quotient types
-- -----------------------------------------------------------------------------

-- | Integer quotient type that has different representations for the same 
--   value internally and exposes the unnormalised representation.
newtype NonCongruentIntMod2 = NCIntMod2 { unNCIntMod2 :: Int }
  
instance Eq NonCongruentIntMod2 where
  (NCIntMod2 n) == (NCIntMod2 m) = mod n 2 == mod m 2
  
instance Ord NonCongruentIntMod2 where
  compare (NCIntMod2 n) (NCIntMod2 m) = compare (mod n 2) (mod m 2)
  
instance Show NonCongruentIntMod2 where
  show (NCIntMod2 n) = "NC-" ++ show n ++ "%2"

instance Arbitrary NonCongruentIntMod2 where
  arbitrary = NCIntMod2 . abs <$> arbitrary

-- | This is where the generation of non-congruent functions happens.
instance CoArbitrary NonCongruentIntMod2 where
  coarbitrary (NCIntMod2 n) = coarbitrary n

instance Function NonCongruentIntMod2 where
  function f = functionMap (\(NCIntMod2 n) -> n) NCIntMod2 f









