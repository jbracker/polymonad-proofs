
open import Level
open import Function using ( _$_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Functor.Definition

module Theory.Functor.Application where

private
  module BiFunctorUnitApplication {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                                  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} where
    open import Data.Product
    open import Data.Unit
    
    [⊤,_] : Functor (⊤-Cat ×C C) D → Functor C D
    [⊤,_] (functor F₀ F₁ id compose)
      = functor (λ x → F₀ (tt , x)) (λ f → F₁ (tt , f)) id compose

    [_,⊤] : Functor (C ×C ⊤-Cat) D → Functor C D
    [_,⊤] (functor F₀ F₁ id compose)
      = functor (λ x → F₀ (x , tt)) (λ f → F₁ (f , tt)) id compose

open BiFunctorUnitApplication public

-------------------------------------------------------------------------------
-- Application of objects to bifunctors
-------------------------------------------------------------------------------
module BiFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                 {C : Category {ℓC₀} {ℓC₁}} 
                 {D : Category {ℓD₀} {ℓD₁}}
                 {E : Category {ℓE₀} {ℓE₁}} where
  open import Data.Product
  open import Data.Unit
  open Category
  private
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    _∘E_ = _∘_ E
  
  constBiFunctor₁ : Obj C → Functor (C ×C D) E → Functor D E
  constBiFunctor₁ x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
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
  
  constBiFunctor₂ : Obj D → Functor (C ×C D) E → Functor C E
  constBiFunctor₂ x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
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
  
  constBiFunctor : Obj C → Obj D → Functor (C ×C D) E → Functor ⊤-Cat E
  constBiFunctor c d (functor F₀ F₁ functor-id compose)
    = functor (λ _ → F₀ (c , d)) (λ _ → F₁ (id C , id D)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ (X , Y)) (sym $ left-id C) (sym $ left-id D)) compose
  
  [_,-]_ = constBiFunctor₁
  [-,_]_ = constBiFunctor₂
  [_,_]_ = constBiFunctor
  
  functorToBiFunctor₁ : Functor C E → Functor (C ×C D) E
  functorToBiFunctor₁ (functor F₀ F₁ fun-id compose) = functor (λ x → F₀ (proj₁ x)) (λ f → F₁ (proj₁ f)) fun-id compose
  
  functorToBiFunctor₂ : Functor D E → Functor (C ×C D) E
  functorToBiFunctor₂ (functor F₀ F₁ fun-id compose) = functor (λ x → F₀ (proj₂ x)) (λ f → F₁ (proj₂ f)) fun-id compose
  
  Bi[_]₁ = functorToBiFunctor₁
  Bi[_]₂ = functorToBiFunctor₂
  
-------------------------------------------------------------------------------
-- Application of objects to trifunctors
-------------------------------------------------------------------------------
module TriFunctor {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                  {A : Category {ℓA₀} {ℓA₁}}
                  {B : Category {ℓB₀} {ℓB₁}}
                  {C : Category {ℓC₀} {ℓC₁}} 
                  {D : Category {ℓD₀} {ℓD₁}} where

  open import Data.Product renaming ( _,_ to _,'_ ; proj₁ to pproj₁ ; proj₂ to pproj₂ )
  open import Theory.Triple
  open Category
  open Triple
  private
    _∘A_ = _∘_ A
    _∘B_ = _∘_ B
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D

  constTriFunctor₂₃ : Obj B → Obj C → Functor (A ×C B ×C C) D → Functor A D
  constTriFunctor₂₃ b c (functor F₀ F₁ functor-id compose)
    = functor (λ a → F₀ (a , b , c)) (λ f → F₁ (f , id B , id C)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ ((g ∘A f) , X , Y)) (sym $ left-id B) (sym $ left-id C)) compose

  constTriFunctor₁₃ : Obj A → Obj C → Functor (A ×C B ×C C) D → Functor B D
  constTriFunctor₁₃ a c (functor F₀ F₁ functor-id compose)
    = functor (λ b → F₀ (a , b , c)) (λ f → F₁ (id A , f , id C)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ (X , (g ∘B f) , Y)) (sym $ left-id A) (sym $ left-id C)) compose
  
  constTriFunctor₁₂ : Obj A → Obj B → Functor (A ×C B ×C C) D → Functor C D
  constTriFunctor₁₂ a b (functor F₀ F₁ functor-id compose)
    = functor (λ c → F₀ (a , b , c)) (λ f → F₁ (id A , id B , f)) functor-id
    $ λ {x} {y} {z} {f} {g} → trans (cong₂ (λ X Y → F₁ (X , Y , (g ∘C f))) (sym $ left-id A) (sym $ left-id B)) compose
  
  [-,_,_]_ = constTriFunctor₂₃
  [_,-,_]_ = constTriFunctor₁₃
  [_,_,-]_ = constTriFunctor₁₂
  
  open Functor

  biFunctorToTriFunctor₁₂ : Functor (A ×C B) D → Functor (A ×C B ×C C) D
  biFunctorToTriFunctor₁₂ (functor F₀ F₁ fun-id compose)
    = functor (λ x → F₀ (proj₁ x ,' proj₂ x)) (λ f → F₁ (proj₁ f ,' proj₂ f)) fun-id compose
    
  biFunctorToTriFunctor₂₃ : Functor (B ×C C) D → Functor (A ×C B ×C C) D
  biFunctorToTriFunctor₂₃ (functor F₀ F₁ fun-id compose) 
    = functor (λ x → F₀ (proj₂ x ,' proj₃ x)) (λ f → F₁ (proj₂ f ,' proj₃ f)) fun-id compose

  biFunctorToTriFunctor₁₃ : Functor (A ×C C) D → Functor (A ×C B ×C C) D
  biFunctorToTriFunctor₁₃ (functor F₀ F₁ fun-id compose) 
    = functor (λ x → F₀ (proj₁ x ,' proj₃ x)) (λ f → F₁ (proj₁ f ,' proj₃ f)) fun-id compose

  Tri[_]₁₂ = biFunctorToTriFunctor₁₂
  Tri[_]₂₃ = biFunctorToTriFunctor₂₃
  Tri[_]₁₃ = biFunctorToTriFunctor₁₃
  
  functorToTriFunctor₁ : Functor A D → Functor (A ×C B ×C C) D
  functorToTriFunctor₁ (functor F₀ F₁ fun-id compose) = functor (λ x → F₀ (proj₁ x)) (λ f → F₁ (proj₁ f)) fun-id compose
  
  functorToTriFunctor₂ : Functor B D → Functor (A ×C B ×C C) D
  functorToTriFunctor₂ (functor F₀ F₁ fun-id compose) = functor (λ x → F₀ (proj₂ x)) (λ f → F₁ (proj₂ f)) fun-id compose
  
  functorToTriFunctor₃ : Functor C D → Functor (A ×C B ×C C) D
  functorToTriFunctor₃ (functor F₀ F₁ fun-id compose) = functor (λ x → F₀ (proj₃ x)) (λ f → F₁ (proj₃ f)) fun-id compose

  Tri[_]₁ = functorToTriFunctor₁
  Tri[_]₂ = functorToTriFunctor₂
  Tri[_]₃ = functorToTriFunctor₃
