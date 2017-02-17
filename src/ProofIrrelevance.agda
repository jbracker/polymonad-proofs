 
module ProofIrrelevance where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Congruence

-------------------------------------------------------------------------------
-- Definition of proof irrelevance
-------------------------------------------------------------------------------

-- A proof irrelevant type is given if you know that any two proof can be made equal.
ProofIrrelevance : {ℓ : Level} → Set ℓ → Set ℓ
ProofIrrelevance P = (x y : P) → x ≡ y

-------------------------------------------------------------------------------
-- Proof irrelevance of certain predefined types
-------------------------------------------------------------------------------

-- Proofs of the empty type are irrelevant.
proof-irr-⊥ : ProofIrrelevance ⊥
proof-irr-⊥ () ()

-- Proofs of the unit type are irrelevant.
proof-irr-⊤ : ProofIrrelevance ⊤
proof-irr-⊤ tt tt = refl

-- Proofs of lifted types are irrelevant if the lifted type has irrelevant proofs.
proof-irr-Lift : {ℓA ℓL : Level} {A : Set ℓA} 
               → ProofIrrelevance A → ProofIrrelevance (Lift {ℓ = ℓL} A)
proof-irr-Lift proof-irr-A (lift a) (lift b) = cong lift (proof-irr-A a b)

-- Proofs of the negation of any proposition are irrelevant (if we have function extensionality).
proof-irr-¬ : {ℓ : Level} {A : Set ℓ} → ProofIrrelevance (¬ A)
proof-irr-¬ ¬a ¬b = fun-ext (λ x → proof-irr-⊥ (¬a x) (¬b x))

-- Proofs of dependent products are irrelevant if the proofs of their components are irrelevant.
proof-irr-Σ : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB}
            → ProofIrrelevance A → ((a : A) → ProofIrrelevance (B a))
            → ProofIrrelevance (Σ A B)
proof-irr-Σ proof-irr-A proof-irr-B (a₁ , b₁) (a₂ , b₂) with proof-irr-A a₁ a₂
proof-irr-Σ proof-irr-A proof-irr-B (a₁ , b₁) (.a₁ , b₂) | refl with proof-irr-B a₁ b₁ b₂
proof-irr-Σ proof-irr-A proof-irr-B (a₁ , b₁) (.a₁ , .b₁) | refl | refl = refl

-- Proofs of non-dependent products are irrelevant if the proofs of their components are irrelevant.
proof-irr-× : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB}
            → ProofIrrelevance A → ProofIrrelevance B
            → ProofIrrelevance (A × B)
proof-irr-× proof-irr-A proof-irr-B a b = proof-irr-Σ proof-irr-A (λ _ → proof-irr-B) a b

-- Proofs of proof irrelevance are irrelevant.
proof-irr-ProofIrrelevance : {ℓA : Level} {A : Set ℓA} → ProofIrrelevance (ProofIrrelevance A)
proof-irr-ProofIrrelevance proof-irr-A proof-irr-A' 
  = fun-ext (λ a → fun-ext (λ b → proof-irrelevance (proof-irr-A a b) (proof-irr-A' a b)))

-- Reexport proof irrelevance for propositional and heterogeneous equality.
open import Relation.Binary.PropositionalEquality as PE
proof-irr-≡ = PE.proof-irrelevance

open import Relation.Binary.HeterogeneousEquality as HE
proof-irr-≅ = HE.proof-irrelevance

-------------------------------------------------------------------------------
-- Definition of Propositions which are sets that are proof irrelevant
-------------------------------------------------------------------------------

-- A proof irrelevant set carries it proof irrelevance around with itself.
PropSet : (ℓ : Level) → Set (lsuc ℓ)
PropSet ℓ = Σ (Set ℓ) ProofIrrelevance

-- A definition of subset that has proof irrelevance.
PropSubsetOf : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
PropSubsetOf {ℓ} X = X → PropSet ℓ

-- Type of proofs that an element is in the set.
_∈_ : ∀ {ℓ} {X : Set ℓ} → (x : X) → (S : PropSubsetOf X) → Set ℓ
x ∈ S = proj₁ (S x)

-- Get the proof irrelevance for the proofs that elements are in a subset.
proof-irr-PropSubset : ∀ {ℓ} {X : Set ℓ} → (S : PropSubsetOf X) → (x : X) → ProofIrrelevance (x ∈ S)
proof-irr-PropSubset {ℓ} {X} S x x∈S y∈S = proj₂ (S x) x∈S y∈S
