
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )
open import Relation.Binary using ( Decidable ; IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell hiding ( Type )

open import Theory.Category
open import Theory.Category.Dependent
open import Theory.Category.Closed
open import Theory.Category.Examples

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Examples.SetApplicative where 

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Product
open import Theory.Haskell.Constrained.Examples.SetFunctor

open DependentCategory

ConstraintMonoidalCategoryLSet : {ℓ : Level} → MonoidalConstraintCategory {ℓ} {suc (suc ℓ)}
ConstraintMonoidalCategoryLSet = record
  { DC = ConstraintCategoryLSet
  ; _Dep⊗₀_ = ProdCt
  ; _Dep⊗₁_ = λ _ _ → tt
  ; depUnit = TheCt (Ord-⊤ , IsStructuralEquality-⊤)
  ; dep-tensor-id = refl
  ; dep-tensor-compose = refl
  ; dep-α = λ x' y' z' → tt
  ; dep-α-inv = λ x' y' z' → tt
  ; dep-λ = λ x' → tt
  ; dep-λ-inv = λ x' → tt
  ; dep-ρ = λ x' → tt
  ; dep-ρ-inv = λ x' → tt
  ; dep-α-natural = refl
  ; dep-λ-natural = refl
  ; dep-ρ-natural = refl
  ; dep-α-left-id = λ a' b' c' → refl
  ; dep-α-right-id = λ a' b' c' → refl
  ; dep-λ-left-id = λ a' → refl
  ; dep-λ-right-id = λ a' → refl
  ; dep-ρ-left-id = λ a' → refl
  ; dep-ρ-right-id = λ a' → refl
  ; dep-triangle-id = λ x' y' → refl
  ; dep-pentagon-id = λ w' x' y' z' → refl
  }
