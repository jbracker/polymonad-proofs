 
module ProofIrrelevance where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- A proof irrelevant type is given if you know that any two proof can be made equal.
ProofIrrelevance : {ℓ : Level} → Set ℓ → Set ℓ
ProofIrrelevance P = (x y : P) → x ≡ y

-- A proof irrelevant set carries it proof irrelevance around with itself.
PropSet : (ℓ : Level) → Set (lsuc ℓ)
PropSet ℓ = ∃ λ (P : Set ℓ) → ProofIrrelevance P

-- A definition of subset that has proof irrelevance.
PropSubsetOf : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
PropSubsetOf {ℓ} X = X → PropSet ℓ

-- Type of proofs that an element is in the set.
_∈_ : ∀ {ℓ} {X : Set ℓ} → (x : X) → (S : PropSubsetOf X) → Set ℓ
x ∈ S = proj₁ (S x)

-- Get the proof irrelevance for the proofs that elements are in a subset.
subset-proof-irr : ∀ {ℓ} {X : Set ℓ} → (S : PropSubsetOf X) → {x y : X} → (x≡y : x ≡ y) → (x∈S : x ∈ S) → (y∈S : y ∈ S) → subst (λ X → X ∈ S) x≡y x∈S ≡ y∈S
subset-proof-irr {ℓ} {X} S {x} {.x} refl x∈S y∈S = proj₂ (S x) x∈S y∈S
