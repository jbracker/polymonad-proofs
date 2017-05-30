
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition
open import Theory.Functor.Definition

module Theory.Functor.Constant where

open Category

constFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} → (C : Category {ℓC₀} {ℓC₁}) → (D : Category {ℓD₀} {ℓD₁}) → Obj D  → Functor C D
constFunctor C D d = functor (λ _ → d) (λ _ → id D {d}) refl (sym (left-id D))
