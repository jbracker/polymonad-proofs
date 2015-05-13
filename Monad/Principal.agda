
module Monad.Principal where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Haskell
open import Identity
open import Monad
open import Monad.Polymonad
open import Polymonad
open import Polymonad.Principal

Monad→PrincipalPolymonad : ∀ {M : TyCon} → (monad : Monad M) → PrincipalPM (Monad→Polymonad monad)
Monad→PrincipalPolymonad monad F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = inj₁ IdentTC , IdentB   , IdentB   , morph₁
Monad→PrincipalPolymonad monad F (inj₁ IdentTC) (inj₂ MonadTC) morph₁ morph₂ = inj₁ IdentTC , IdentB   , ReturnB  , morph₁
Monad→PrincipalPolymonad monad F (inj₂ MonadTC) (inj₁ IdentTC) morph₁ morph₂ = inj₁ IdentTC , ReturnB  , IdentB   , morph₂
Monad→PrincipalPolymonad monad F (inj₂ MonadTC) (inj₂ MonadTC) morph₁ morph₂ = inj₂ MonadTC , FunctorB , FunctorB , morph₂

