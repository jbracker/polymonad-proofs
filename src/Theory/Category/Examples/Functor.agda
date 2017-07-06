
-- Stdlib
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality

open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Category.Examples.Functor where  

-- Category of functors and natural transformations
functorCategory : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} → Category {Cℓ₀} {Cℓ₁} → Category {Dℓ₀} {Dℓ₁} → Category
functorCategory C D = record
  { Obj = Functor C D
  ; Hom = NaturalTransformation {C = C} {D}
  ; _∘_ = λ {F} {G} {H} → ⟨_⟩∘ᵥ⟨_⟩ {C = C} {D} {F} {G} {H}
  ; id = λ {F} → Id⟨ F ⟩
  ; assoc = λ {a b c d} {f} {g} {h} → assoc' {a} {b} {c} {d} {f} {g} {h}
  ; left-id = λ {a b} {f} → left-id' {a} {b} {f}
  ; right-id = λ {a b} {f} → right-id' {a} {b} {f}
  } where
    abstract
      assoc' : {a b c d : Functor C D} {f : NaturalTransformation a b}
             → {g : NaturalTransformation b c} {h : NaturalTransformation c d}
             → ⟨ h ⟩∘ᵥ⟨ ⟨ g ⟩∘ᵥ⟨ f ⟩ ⟩ ≡ ⟨ ⟨ h ⟩∘ᵥ⟨ g ⟩ ⟩∘ᵥ⟨ f ⟩
      assoc' = natural-transformation-eq $ fun-ext $ λ _ → Category.assoc D

    abstract
      left-id' : {a b : Functor C D} {f : NaturalTransformation a b}
               → ⟨ f ⟩∘ᵥ⟨ Id⟨ a ⟩ ⟩ ≡ f
      left-id' = natural-transformation-eq $ fun-ext $ λ _ → Category.left-id D

    abstract
      right-id' : {a b : Functor C D} {f : NaturalTransformation a b}
                → ⟨ Id⟨ b ⟩ ⟩∘ᵥ⟨ f ⟩ ≡ f
      right-id' = natural-transformation-eq $ fun-ext $ λ _ → Category.right-id D

[_,_] = functorCategory
