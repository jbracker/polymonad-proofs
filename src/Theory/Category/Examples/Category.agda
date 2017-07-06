
-- Stdlib
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition

module Theory.Category.Examples.Category where  

-- Category of categories and functors.
catCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = suc (ℓ₀ ⊔ ℓ₁)} {ℓ₁ = ℓ₀ ⊔ ℓ₁}
catCategory {ℓ₀} {ℓ₁} = record
  { Obj = Category {ℓ₀} {ℓ₁}
  ; Hom = λ C D → Functor C D
  ; _∘_ = [_]∘[_]
  ; id = λ {C} → Id[ C ]
  ; assoc = λ {a b c d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = left-id
  ; right-id = right-id
  } where
    abstract
      assoc : {a b c d : Category {ℓ₀} {ℓ₁}} {f : Functor a b} {g : Functor b c} {h : Functor c d} 
            → [ h ]∘[ [ g ]∘[ f ] ] ≡ [ [ h ]∘[ g ] ]∘[ f ]
      assoc = functor-eq refl refl

    abstract
      right-id : {a b : Category} {f : Functor a b} → [ Id[ b ] ]∘[ f ] ≡ f
      right-id = functor-eq refl refl

    abstract
      left-id : {a b : Category} {f : Functor a b} → [ f ]∘[ Id[ a ] ] ≡ f
      left-id = functor-eq refl refl
