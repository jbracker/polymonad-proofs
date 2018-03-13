 
module Polymonad.Principal where

-- Stdlib
open import Level renaming ( suc to lsuc )
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad.Definition
open import Identity

-- Predicate describing a principal polymonad.
-- This deviates from Hicks original definition in that F may not be empty.
-- This is an important restriction, because otherwise every two elements in 
-- the set of type constructors would have a common lower-bound.
PrincipalPM : ∀ {n} {TyCons : Set n} {Id : TyCons} → Polymonad TyCons Id → Set (lsuc n)
PrincipalPM {n} {TyCons} {Id} pm 
  = (F : SubsetOf (TyCons × TyCons))
  → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F)
  → (M₁ M₂ : TyCons)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₁)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₂)
  → ∃ λ(M̂ : TyCons) 
  → B[ M̂ , Id ] pm ▷ M₁ 
  × B[ M̂ , Id ] pm ▷ M₂ 
  × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)

