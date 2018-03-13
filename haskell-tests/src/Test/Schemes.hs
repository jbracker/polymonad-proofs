
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Schemes 
  ( -- * Constraints
    UnconstrainedCt1, UnconstrainedCt2, UnconstrainedCt3
  , SameCt1, SameCt2, SameCt3
    -- * Shapes for different functions
  , SuperFmap, SuperAp, SuperPure, SuperBind, SuperReturn
  , Fmap, Ap, Pure, Bind, Return
  ) where

import GHC.Exts ( Constraint )

-- -----------------------------------------------------------------------------
-- Constraint synonyms
-- -----------------------------------------------------------------------------

-- | Empty constraint with one argument.
type family UnconstrainedCt1 a :: Constraint where
  UnconstrainedCt1 a = ()

-- | Empty constraint with two argument.
type family UnconstrainedCt2 a b :: Constraint where
  UnconstrainedCt2 a b = ()

-- | Empty constraint with three argument.
type family UnconstrainedCt3 a b c :: Constraint where
  UnconstrainedCt3 a b c = ()

-- | Apply the constraint to the one given type.
type family SameCt1 ct a :: Constraint where
  SameCt1 ct a = (ct a)

-- | Apply the constraint to the two given types.
type family SameCt2 ct a b :: Constraint where
  SameCt2 ct a b = (ct a , ct b)

-- | Apply the constraint to the three given types.
type family SameCt3 ct a b c :: Constraint where
  SameCt3 ct a b c = (ct a , ct b , ct c)

-- -----------------------------------------------------------------------------
-- Types for different functions
-- -----------------------------------------------------------------------------


-- | Very general shape for @ap@-functions.
type SuperAp f g h a b= f (a -> b) -> g a -> h b

-- | Shape for standard @<*>@-operators.
type Ap f a b = SuperAp f f f a b


-- | Very general shape for @>>=@-operators.
type SuperBind m n p a b = m a -> (a -> n b) -> p b

-- | Shape for standard @>>=@-operators.
type Bind m a b = SuperBind m m m a b


-- Very general shape for @fmap@-functions.
type SuperFmap f g a b = (a -> b) -> f a -> g b

-- Shape for standard @fmap@-functions.
type Fmap f a b = SuperFmap f f a b


-- | General shape for @pure@-functions.
type SuperPure f a = a -> f a

-- | General shape for constrained @pure@-functions.
type Pure f a = SuperPure f a

type SuperReturn m a = SuperPure m a
type Return m a = Pure m a





