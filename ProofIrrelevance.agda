 
module ProofIrrelevance where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Utilities using ( funExt )

-- A proof irrelevant type is given if you know that any two proof can be made equal.
ProofIrrelevance : {ℓ : Level} → Set ℓ → Set ℓ
ProofIrrelevance P = (x y : P) → x ≡ y

-- Proofs of the empty type are irrelevant.
proof-irr-⊥ : ProofIrrelevance ⊥
proof-irr-⊥ () ()

-- Proofs of the negation of any proposition are irrelevant (if we have function extensionality).
proof-irr-¬ : {ℓ : Level} {A : Set ℓ} → ProofIrrelevance (¬ A)
proof-irr-¬ ¬a ¬b = funExt (λ x → proof-irr-⊥ (¬a x) (¬b x))


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
proof-irr-PropSubset : ∀ {ℓ} {X : Set ℓ} → (S : PropSubsetOf X) → (x : X) → ProofIrrelevance (x ∈ S)
proof-irr-PropSubset{ℓ} {X} S x x∈S y∈S = proj₂ (S x) x∈S y∈S
