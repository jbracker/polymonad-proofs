
open import Level
open import Function using ( _$_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( cong )

open import Utilities
open import ProofIrrelevance
open import Haskell

open import Theory.Category
open import Theory.Category.Examples
open import Theory.Category.Concrete
open import Theory.Category.Dependent
open import Theory.Category.Subcategory
open import Theory.Category.Subcategory.Examples
open import Theory.Category.Closed.Dependent
open import Theory.Category.Closed.Examples
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples

open import Theory.Functor
 
module Theory.Haskell.Constrained {ℓ : Level} where

-- A constraint category adds constraints on the types and functions involving those types.
-- Therefore, a constraint category is a category that depends on Hask for its definition.
ConstraintCategory : {ℓCt₀ ℓCt₁ : Level} → Set (suc (ℓCt₁ ⊔ ℓCt₀ ⊔ ℓ))
ConstraintCategory {ℓCt₀} {ℓCt₁} = DependentCategory {ℓDep₀ = ℓCt₀} {ℓDep₁ = ℓCt₁} (Hask {ℓ})

ClosedConstraintCategory : {ℓCt₀ ℓCt₁ : Level} → Set (suc (ℓCt₁ ⊔ ℓCt₀ ⊔ ℓ))
ClosedConstraintCategory {ℓCt₀} {ℓCt₁} = DependentClosedCategory {ℓDep₀ = ℓCt₀} {ℓDep₁ = ℓCt₁} (setClosedCategory {ℓ})

MonoidalConstraintCategory : {ℓCt₀ ℓCt₁ : Level} → Set (suc (ℓCt₁ ⊔ ℓCt₀ ⊔ ℓ))
MonoidalConstraintCategory {ℓCt₀} {ℓCt₁} = DependentMonoidalCategory {ℓDep₀ = ℓCt₀} {ℓDep₁ = ℓCt₁} (setMonoidalCategory {ℓ})

open Category
open DependentCategory

-- Delivers the constrained version of Hask using the constraints from the given constraint category.
ConstrainedHask : {ℓCt₀ ℓCt₁ : Level} → (Cts : ConstraintCategory {ℓCt₀} {ℓCt₁}) → Category {suc ℓ ⊔ ℓCt₀} {ℓ ⊔ ℓCt₁}
ConstrainedHask Cts = DepCat Cts

-- The constraint embedding functor takes the elements of a constrained Hask and embeds them into Hask by forgetting the constraints.
ConstraintEmbeddingFunctor : {ℓCt₀ ℓCt₁ : Level} → (Cts : ConstraintCategory {ℓCt₀} {ℓCt₁}) → Functor (ConstrainedHask Cts) Hask
ConstraintEmbeddingFunctor Cts = functor proj₁ proj₁ refl refl

-- Property that a constrained category only has one instance of a constraint per type.
UniqueInstances : {ℓCt₀ ℓCt₁ : Level} → (Cts : ConstraintCategory {ℓCt₀} {ℓCt₁}) → Set (suc ℓ ⊔ ℓCt₀ ⊔ ℓCt₁)
UniqueInstances {ℓCts₀} {ℓCt₁} Cts 
  = ((α : Obj Hask) → ProofIrrelevance (DepObj Cts α)) 
  -- For the homomorphisms the constraints may only depend on the type of the functions, not the functions themselves.
  × ({α β : Obj Hask} → (f g : α → β) → (αCt : DepObj Cts α) → (βCt : DepObj Cts β) → (fCt : DepHom Cts αCt βCt f) → (gCt : DepHom Cts αCt βCt g) → fCt ≅ gCt)

-- A constraint category with unique instances implies that the homomorphisms of the underlying dependent category are unique as well.
UniqueInstances→DependentHomUniqueness : {ℓCt₀ ℓCt₁ : Level} 
                                       → (CC : ConstraintCategory {ℓCt₀} {ℓCt₁}) → UniqueInstances CC 
                                       → DependentHomUniqueness CC
UniqueInstances→DependentHomUniqueness CC (unique-obj-inst , unique-hom-inst) {a₁ , a₂} {b₁ , b₂} (f₁ , f₂) (.f₁ , g₂) refl = unique-hom-inst f₁ f₁ a₂ b₂ f₂ g₂

-- A constraint category with unique instances implies that the objects of the underlying dependent category are unique as well.
UniqueInstances→DependentObjUniqueness : {ℓCt₀ ℓCt₁ : Level} 
                                       → (CC : ConstraintCategory {ℓCt₀} {ℓCt₁}) → UniqueInstances CC 
                                       → DependentObjUniqueness CC
UniqueInstances→DependentObjUniqueness CC (unique-obj-inst , unique-hom-inst) {a₁ , a₂} {.a₁ , b₂} refl = ≡-to-≅ (unique-obj-inst a₁ a₂ b₂)

-- Every constraint category is an instance of a concrete category if the dependent homomorphisms it uses are uniquely determined.
ConstraintCategory→ConcreteCategory : {ℓCt₀ ℓCt₁ : Level} 
                                    → (CC : ConstraintCategory {ℓCt₀} {ℓCt₁}) → DependentHomUniqueness CC 
                                    → IsConcreteCategory {ℓ} {suc ℓ ⊔ ℓCt₀} {ℓ ⊔ ℓCt₁} (ConstrainedHask CC)
ConstraintCategory→ConcreteCategory CC dep-hom-unique = ConstraintEmbeddingFunctor CC , faithful
  where
    faithful : IsFaithfulFunctor (ConstraintEmbeddingFunctor CC)
    faithful (a₁ , a₂) (b₁ , b₂) (f₁ , f₂) (.f₁ , g₂) refl = cong (_,_ f₁) (≅-to-≡ (dep-hom-unique (f₁ , f₂) (f₁ , g₂) refl))

-- Proof that the embedding functor for a constraint category is injective if the 
-- instances are unique (which should always be true in Haskell).
constraint-embedding-functor-is-injective : {ℓCt₀ ℓCt₁ : Level} 
                                          → (Cts : ConstraintCategory {ℓCt₀} {ℓCt₁}) 
                                          → UniqueInstances Cts
                                          → IsInjectiveFunctor (ConstraintEmbeddingFunctor Cts)
constraint-embedding-functor-is-injective Cts (uniqueObjInsts , uniqueHomInsts) = IsInjectiveF₀ , IsInjectiveF₁
    where
      EmbeddingFunctor = ConstraintEmbeddingFunctor Cts
      
      IsInjectiveF₀ : IsInjective (Functor.F₀ EmbeddingFunctor)
      IsInjectiveF₀ (α , αCts) (.α , βCts) refl = cong (λ X → α , X) (uniqueObjInsts α αCts βCts)
      
      IsInjectiveF₁ : (α β : Obj (DepCat Cts)) → IsInjective (Functor.F₁ EmbeddingFunctor)
      IsInjectiveF₁ (α , αCts) (β , βCts) (f , fCt) (.f , gCt) refl = cong (λ X → f , X) (≅-to-≡ $ uniqueHomInsts f f αCts βCts fCt gCt)

-- Proof that the embedding of the 'ConstraintCategory' actually provides a subcategory of Haskell.
constraint-category-embedding-is-subcategory : {ℓCt₀ ℓCt₁ : Level} 
                                             → (Cts : ConstraintCategory {ℓCt₀} {ℓCt₁}) 
                                             → UniqueInstances Cts
                                             → Subcategory (liftCategory Hask)
constraint-category-embedding-is-subcategory Cts uniqueInsts 
  = EmbeddingFunctor→LiftSubcategory (ConstraintEmbeddingFunctor Cts) (constraint-embedding-functor-is-injective Cts uniqueInsts)
