
-- | Functions for checking equality between types that do not have a
--   proper 'Eq' instance.
module Test.Equality
  ( funext_eq1
  , funext_eq2
  , funext_eq3
  ) where

-- | Approximate equality for two functions with one argument using function extensionality.
funext_eq1 :: (Eq b) => (a -> b) -> (a -> b) -> (a -> Bool)
funext_eq1 f g a = f a == g a

-- | Approximate equality for two functions with two arguments using function extensionality.
funext_eq2 :: (Eq c) => (a -> b -> c) -> (a -> b -> c) -> (a -> b -> Bool)
funext_eq2 f g a b = f a b == g a b

-- | Approximate equality for two functions with three arguments using function extensionality.
funext_eq3 :: (Eq d) => (a -> b -> c -> d) -> (a -> b -> c -> d) -> (a -> b -> c -> Bool)
funext_eq3 f g a b c = f a b c == g a b c