
module Theory.ProofIrrelevance where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

ProofIrrelevance : ∀ {ℓ ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B → Set ℓ) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
ProofIrrelevance {A = A} {B = B}  _≈_ = {a : A} → {b : B} → (p : a ≈ b) → (q : a ≈ b) → p ≡ q
