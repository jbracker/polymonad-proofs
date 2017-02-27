
open import Level
open import Function using ( _$_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category
open import Theory.Functor

module Theory.Functor.Application where

-------------------------------------------------------------------------------
-- Application of objects to bifunctors
-------------------------------------------------------------------------------
module BiFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                 {C : Category {ℓC₀} {ℓC₁}} 
                 {D : Category {ℓD₀} {ℓD₁}}
                 {E : Category {ℓE₀} {ℓE₁}} where
  open import Data.Product
  open Category
  private
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    _∘E_ = _∘_ E
  
  [_,-]_ : Obj C → Functor (C ×C D) E → Functor D E
  [_,-]_ x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
    where
      ObjF : Obj D → Obj E
      ObjF d = F₀ (x , d)
      
      HomF : {a b : Obj D} → Hom D a b → Hom E (ObjF a) (ObjF b)
      HomF f = F₁ (id C {x} , f)
      
      composeF : {a b c : Obj D} {f : Hom D a b} {g : Hom D b c}
               → HomF (g ∘D f) ≡ HomF g ∘E HomF f
      composeF {a} {b} {c} {f} {g} = begin
        F₁ (id C {x} , g ∘D f)
          ≡⟨ cong (λ X → F₁ (X , g ∘D f)) (sym $ left-id C) ⟩
        F₁ (id C {x} ∘C id C {x} , g ∘D f)
          ≡⟨ compose ⟩
        F₁ (id C {x} , g) ∘E F₁ (id C {x} , f) ∎
  
  [-,_]_ : Obj D → Functor (C ×C D) E → Functor C E
  [-,_]_ x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
    where
      ObjF : Obj C → Obj E
      ObjF c = F₀ (c , x)
      
      HomF : {a b : Obj C} → Hom C a b → Hom E (ObjF a) (ObjF b)
      HomF f = F₁ (f , id D {x})
      
      composeF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
               → HomF (g ∘C f) ≡ HomF g ∘E HomF f
      composeF {a} {b} {c} {f} {g} = begin
        F₁ (g ∘C f , id D {x})
          ≡⟨ cong (λ X → F₁ (g ∘C f , X)) (sym $ left-id D) ⟩
        F₁ (g ∘C f , id D {x} ∘D id D {x})
          ≡⟨ compose ⟩
        F₁ (g , id D {x}) ∘E F₁ (f , id D {x}) ∎
  
-------------------------------------------------------------------------------
-- Application of objects to trifunctors
-------------------------------------------------------------------------------
module TriFunctor {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                  {A : Category {ℓA₀} {ℓA₁}}
                  {B : Category {ℓB₀} {ℓB₁}}
                  {C : Category {ℓC₀} {ℓC₁}} 
                  {D : Category {ℓD₀} {ℓD₁}} where
  open import Theory.Triple
  open Category
  private
    _∘A_ = _∘_ A
    _∘B_ = _∘_ B
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D

  [-,_,_]_ : Obj B → Obj C → Functor (A ×C B ×C C) D → Functor A D
  [-,_,_]_ b c (functor F₀ F₁ functor-id compose)
    = functor (λ a → F₀ (a , b , c)) (λ f → F₁ (f , id B , id C)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ ((g ∘A f) , X , Y)) (sym $ left-id B) (sym $ left-id C)) compose

  [_,-,_]_ : Obj A → Obj C → Functor (A ×C B ×C C) D → Functor B D
  [_,-,_]_ a c (functor F₀ F₁ functor-id compose)
    = functor (λ b → F₀ (a , b , c)) (λ f → F₁ (id A , f , id C)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ (X , (g ∘B f) , Y)) (sym $ left-id A) (sym $ left-id C)) compose
  
  [_,_,-]_ : Obj A → Obj B → Functor (A ×C B ×C C) D → Functor C D
  [_,_,-]_ a b (functor F₀ F₁ functor-id compose)
    = functor (λ c → F₀ (a , b , c)) (λ f → F₁ (id A , id B , f)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ (X , Y , (g ∘C f))) (sym $ left-id A) (sym $ left-id B)) compose
