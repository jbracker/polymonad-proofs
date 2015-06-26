 
module Polymonad.Principal where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Haskell
open import Polymonad
open import Identity

-- Formalization of a subsets for a given set.
SubsetOf : Type → Set₁
SubsetOf X = X → Set

-- An element is in the subset, if the subset predicate is true.
_∈_ : ∀ {X : Type} → (x : X) → (S : SubsetOf X) → Set
x ∈ S = S x

-- Predicate describing a principal polymonad.
PrincipalPM : ∀ {TyCons : Set} {Id : TyCons} →  Polymonad TyCons Id → Set₁
PrincipalPM {TyCons} {Id} pm 
  = (F : SubsetOf (TyCons × TyCons))
  → (M₁ M₂ : TyCons)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₁)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₂)
  → ∃ λ(M̂ : TyCons) 
  → B[ M̂ , Id ] pm ▷ M₁ 
  × B[ M̂ , Id ] pm ▷ M₂ 
  × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)

