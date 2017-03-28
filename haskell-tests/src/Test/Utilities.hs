
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Test.Utilities
  ( check, checkAll2, checkAll3
  , (&&&&)
  ) where

import Data.Proxy ( Proxy(..) )
import Data.Typeable

import Test.QuickCheck
import Test.QuickCheck.Function

data Test = Test
  { fails :: Bool
  , name :: String
  , test :: forall a t. (Testable t) => Proxy a -> t
  }

-- Helpers for checking laws...
infixl 1 &&&&

(&&&&) :: IO Result -> IO Result -> IO Result
m1 &&&& m2 = do
  res <- m1
  case res of
    Success {} -> m2
    _ -> return res

check :: (Typeable a, Show a, Testable t) => Int -> Proxy a -> String -> (Proxy a -> t) -> IO Result
check n p name law = do
  putStrLn $ "> " ++ name ++ ": " ++ show (typeRep p)
  quickCheckWithResult (stdArgs { maxSuccess = n, maxDiscardRatio = 10 }) (law p)

checkAll2 :: forall a b.
  ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a
  , Function b, CoArbitrary b, Arbitrary b, Typeable b, Show b
  ) => Proxy (a, b)
  -> (forall c d. ( Function c, CoArbitrary c, Arbitrary c, Typeable c, Show c
                  , Function d, CoArbitrary d, Arbitrary d, Typeable d, Show d
                  ) => Proxy (c, d) -> IO Result)
  -> IO Result
checkAll2 Proxy chck = chck (Proxy :: Proxy (a,b))
                  &&&& chck (Proxy :: Proxy (b,a))
                  &&&& chck (Proxy :: Proxy (a,a))
                  &&&& chck (Proxy :: Proxy (b,b))

checkAll3 :: forall a b c. 
  ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a
  , Function b, CoArbitrary b, Arbitrary b, Typeable b, Show b
  , Function c, CoArbitrary c, Arbitrary c, Typeable c, Show c
  ) => Proxy (a,b,c) 
  -> (forall d e f. ( Function d, CoArbitrary d, Arbitrary d, Typeable d, Show d
                    , Function e, CoArbitrary e, Arbitrary e, Typeable e, Show e
                    , Function f, CoArbitrary f, Arbitrary f, Typeable f, Show f
                    ) => Proxy (d,e,f) -> IO Result) 
  -> IO Result
checkAll3 Proxy chck = chck (Proxy :: Proxy (a,b,c))
                  &&&& chck (Proxy :: Proxy (a,c,b))
                  &&&& chck (Proxy :: Proxy (b,a,c))
                  &&&& chck (Proxy :: Proxy (b,c,a))
                  &&&& chck (Proxy :: Proxy (c,a,b))
                  &&&& chck (Proxy :: Proxy (c,b,c))
                  &&&& chck (Proxy :: Proxy (a,a,a))
                  &&&& chck (Proxy :: Proxy (b,b,b))
                  &&&& chck (Proxy :: Proxy (c,c,c))
                  &&&& chck (Proxy :: Proxy (a,a,b))
                  &&&& chck (Proxy :: Proxy (a,a,c))
                  &&&& chck (Proxy :: Proxy (a,b,b))
                  &&&& chck (Proxy :: Proxy (a,c,c))
                  &&&& chck (Proxy :: Proxy (b,b,a))
                  &&&& chck (Proxy :: Proxy (b,b,c))
                  &&&& chck (Proxy :: Proxy (b,a,a))
                  &&&& chck (Proxy :: Proxy (b,c,c))
                  &&&& chck (Proxy :: Proxy (c,c,a))
                  &&&& chck (Proxy :: Proxy (c,c,b))
                  &&&& chck (Proxy :: Proxy (c,a,a))
                  &&&& chck (Proxy :: Proxy (c,b,b))