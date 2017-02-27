
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Application
open import Theory.Natural.Transformation

open TriFunctor

module Theory.Natural.ExtranaturalTransformation where

-------------------------------------------------------------------------------
-- Definition of extranatural transformations
-------------------------------------------------------------------------------
record ExtranaturalTransformation {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                                  {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
                                  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                  (F : Functor (A ×C B op ×C B) D)
                                  (G : Functor (A ×C C op ×C C) D)
                                  : Set (ℓA₀ ⊔  ℓA₁ ⊔ ℓC₀ ⊔ ℓC₁ ⊔ ℓB₀ ⊔ ℓB₁ ⊔ ℓD₁) where
  open Category
  private
    _∘D_ = _∘_ D
  field
    η : (a : Obj A) → (b : Obj B) → (c : Obj C)
      → Hom D ([ F ]₀ (a , b , b)) ([ G ]₀ (a , c , c))
    
    η-natural : (b : Obj B) → (c : Obj C)
              → {x y : Obj A} {f : Hom A x y}
              → ([ ([-, c , c ] G) ]₁ f) ∘D η x b c ≡ η y b c ∘D ([ ([-, b , b ] F) ]₁ f)
            -- G₁ f ∘ η ≡ η ∘ F₁ f
  
  η-natural-transformation : (b : Obj B) → (c : Obj C)
                           → NaturalTransformation ([-, b , b ] F) ([-, c , c ] G)
  η-natural-transformation b c = naturalTransformation (λ a → η a b c) (η-natural b c)

  field
    extranatural : (a : Obj A) → (b : Obj B) → {c c' : Obj C} → (f : Hom C c c')
                 → [ G ]₁ (id A , f         , id C) ∘D η a b c'
                 ≡ [ G ]₁ (id A , id (C op) , f   ) ∘D η a b c
    
    extranatural-op : (a : Obj A) → (c : Obj C) → {b b' : Obj B} → (f : Hom B b b')
                    → η a b' c ∘D [ F ]₁ (id A , id (B op) , f   )
                    ≡ η a b  c ∘D [ F ]₁ (id A , f         , id B)
