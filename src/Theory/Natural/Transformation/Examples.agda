
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation


module Theory.Natural.Transformation.Examples where

open Category
open Functor
     
     
functorAssociator : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                  → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
                  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                  → (F : Functor C D)
                  → (G : Functor B C)
                  → (H : Functor A B)
                  → NaturalTransformation [ F ]∘[ [ G ]∘[ H ] ] [ [ F ]∘[ G ] ]∘[ H ]
functorAssociator {A = A} {B} {C} {D} F G H = naturalTransformation η nat
  where
    _∘D_ = _∘_ D
    
    η : (x : Obj A) → Hom D ([ [ F ]∘[ [ G ]∘[ H ] ] ]₀ x) ([ [ [ F ]∘[ G ] ]∘[ H ] ]₀ x)
    η x = Category.id D {[ F ]₀ ([ G ]₀ ([ H ]₀ x))}
    
    abstract
      nat : {a b : Obj A} {f : Hom A a b}
          → [ [ [ F ]∘[ G ] ]∘[ H ] ]₁ f ∘D (η a) ≡ η b ∘D [ [ F ]∘[ [ G ]∘[ H ] ] ]₁ f
      nat = trans (left-id D) (sym (right-id D))

functorAssociator' : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                   → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
                   → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                   → (F : Functor C D)
                   → (G : Functor B C)
                   → (H : Functor A B)
                   → NaturalTransformation [ [ F ]∘[ G ] ]∘[ H ] [ F ]∘[ [ G ]∘[ H ] ]
functorAssociator' {A = A} {B} {C} {D} F G H = naturalTransformation η nat
  where
    _∘D_ = _∘_ D
    
    η : (x : Obj A) → Hom D  ([ [ [ F ]∘[ G ] ]∘[ H ] ]₀ x) ([ [ F ]∘[ [ G ]∘[ H ] ] ]₀ x)
    η x = Category.id D {[ F ]₀ ([ G ]₀ ([ H ]₀ x))}
                                                
    abstract
      nat : {a b : Obj A} {f : Hom A a b}
          → [ [ F ]∘[ [ G ]∘[ H ] ] ]₁ f ∘D (η a) ≡ η b ∘D [ [ [ F ]∘[ G ] ]∘[ H ] ]₁ f
      nat = trans (left-id D) (sym (right-id D))
