
open import Level

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Functor.Definition

module Theory.Functor.Composition where

-------------------------------------------------------------------------------
-- Composition of Functors
-------------------------------------------------------------------------------
compFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
            → Functor D E → Functor C D → Functor C E
compFunctor {C = C} {D = D} {E = E} F G = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = id
  ; compose = compose
  } where
    open Category hiding ( id )
    F₀ : Obj C → Obj E
    F₀ a = [ F ]₀ ( [ G ]₀ a )
    
    F₁ : {a b : Obj C} → Hom C a b → Hom E (F₀ a) (F₀ b)
    F₁ f = [ F ]₁ ( [ G ]₁ f )
    
    id : ∀ {a : Obj C} → F₁ {a = a} (Category.id C) ≡ Category.id E
    id = trans (cong (λ X → Functor.F₁ F X) (Functor.id G)) (Functor.id F)
    
    compose : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
         → F₁ (_∘_ C g f) ≡ _∘_ E (F₁ g) (F₁ f)
    compose = trans (cong (λ X → Functor.F₁ F X) (Functor.compose G)) (Functor.compose F)

[_]∘[_] = compFunctor

-------------------------------------------------------------------------------
-- Composition of BiFunctors
-------------------------------------------------------------------------------
module BiFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level}
                 {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}where
  open import Data.Product renaming ( _,_ to _,'_ )

  open Category

  private
    _∘E_ = _∘_ E
  
  [_,_]∘[_] : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
            → Functor A C → Functor B D
            → Functor (C ×C D) E → Functor (A ×C B) E
  [_,_]∘[_] {A = A} {B} F G Bi
    = functor ObjH HomH
              (trans (cong₂ (λ X Y → [ Bi ]₁ (X ,' Y)) (Functor.id F) (Functor.id G)) (Functor.id Bi))
              (trans (cong₂ (λ X Y → [ Bi ]₁ (X ,' Y)) (Functor.compose F) (Functor.compose G)) (Functor.compose Bi))
    where
      ObjH : Category.Obj (A ×C B) → Category.Obj E
      ObjH (a ,' b) = [ Bi ]₀ ([ F ]₀ a ,' [ G ]₀ b)

      HomH : {x y : Obj (A ×C B)} → Hom (A ×C B) x y → Hom E (ObjH x) (ObjH y)
      HomH (f ,' g) = [ Bi ]₁ ([ F ]₁ f ,' [ G ]₁ g )

  [_,-]∘[_] : {ℓA₀ ℓA₁ : Level} {A : Category {ℓA₀} {ℓA₁}}
            → Functor A C
            → Functor (C ×C D) E → Functor (A ×C D) E
  [_,-]∘[_] F Bi = [ F , Id[ D ] ]∘[ Bi ]
  
  [-,_]∘[_] : {ℓB₀ ℓB₁ : Level} {B : Category {ℓB₀} {ℓB₁}}
            → Functor B D
            → Functor (C ×C D) E → Functor (C ×C B) E
  [-,_]∘[_] F Bi = [ Id[ C ] , F ]∘[ Bi ]
