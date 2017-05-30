
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

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Examples

open import Theory.Functor.Definition

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Applicative

module Theory.Haskell.Constrained.Examples.SetApplicative {ℓ : Level} where 

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Product
open import Theory.Haskell.Constrained.Examples.SetFunctor.Map
open import Theory.Haskell.Constrained.Examples.SetFunctor.Instances
open import Theory.Haskell.Constrained.Examples.SetFunctor

open DependentCategory

ConstraintMonoidalCategoryLSet : MonoidalConstraintCategory {ℓ} {suc (suc ℓ)}
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

unions : {A : Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})} → LSet (LSet A , OrdLSet {ℓ} {A}) → LSet A
unions (lset [] (lift tt)) = lset [] (lift tt)
unions (lset (x ∷ xs) (proj₁ , sortedXs)) = {!proj₁!}

ApplicativeLSet : ConstrainedApplicative ConstraintMonoidalCategoryLSet
ApplicativeLSet = record
  { CtsFunctor = FunctorLSet
  ; unit = lset [] (lift tt)
  ; prod-map = prod-map
  ; naturality = {!!}
  ; associativity = {!!}
  ; left-unitality = {!!}
  ; right-unitality = {!!}
  } where
    F₀ = Functor.F₀ (ConstrainedFunctor.CtFunctor FunctorLSet)
    _⊗₀_ = MonoidalCategory._⊗₀_ (DependentMonoidalCategory.DepMonCat ConstraintMonoidalCategoryLSet)
    
    DC = DepCat (DependentMonoidalCategory.DC ConstraintMonoidalCategoryLSet)
    
    prod-map : (x y : Category.Obj DC) → F₀ x × F₀ y → F₀ (x ⊗₀ y)
    prod-map (A , CtA) (B , CtB) (lset xs sortedXs , lset ys sortedYs) = {!!}
