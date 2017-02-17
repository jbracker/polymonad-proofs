 
module Theory.MonoidalCategory where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Data.Product renaming ( _,_ to _,'_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using ( _≅_ )

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalIsomorphism

module FunctorApplication {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where
  
  open Category renaming ( id to idC )
  open Functor renaming ( id to idF )
  
  private
    _∘CCC_ = _∘_ (C ×C C ×C C)
    _∘C_ = _∘_ C
  
  -- ((_ ⊗ _) ⊗ _) ⇒ _
  associatorL : Functor (C ×C C) C → Functor (C ×C C ×C C) C
  associatorL F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj (C ×C C ×C C) → Obj C
      G₀ (a , b , c) = F₀ F (F₀ F (a ,' b) ,' c)
      
      G₁ : {a b : Obj (C ×C C ×C C)} → Hom (C ×C C ×C C) a b → Hom C (G₀ a) (G₀ b)
      G₁ (f , g , h) = F₁ F (F₁ F (f ,' g) ,' h)
      
      idG : {a : Obj (C ×C C ×C C)} → G₁ {a} {a} (idC (C ×C C ×C C)) ≡ idC C
      idG = trans (cong (λ X → F₁ F (X ,' idC C)) (idF F)) (idF F)
      
      composeG : {a b c : Obj (C ×C C ×C C)} 
               → {f : Hom (C ×C C ×C C) a b} {g : Hom (C ×C C ×C C) b c}
               → G₁ (g ∘CCC f) ≡ (G₁ g) ∘C (G₁ f)
      composeG {f = f₁ , f₂ , f₃} {g = g₁ , g₂ , g₃} 
        = trans (cong (λ X → F₁ F (X ,' g₃ ∘C f₃)) (compose F)) (compose F)
  
  -- (_ ⊗ (_ ⊗ _)) ⇒ _
  associatorR : Functor (C ×C C) C → Functor (C ×C C ×C C) C 
  associatorR F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj (C ×C C ×C C) → Obj C
      G₀ (a , b , c) = F₀ F (a ,' F₀ F (b ,' c))
     
      G₁ : {a b : Obj (C ×C C ×C C)} → Hom (C ×C C ×C C) a b → Hom C (G₀ a) (G₀ b)
      G₁ (f , g , h) = F₁ F (f ,' F₁ F (g ,' h))
      
      idG : {a : Obj (C ×C C ×C C)} → G₁ {a} {a} (idC (C ×C C ×C C)) ≡ idC C
      idG = trans (cong (λ X → F₁ F (idC C ,' X)) (idF F)) (idF F)
      
      composeG : {a b c : Obj (C ×C C ×C C)} 
               → {f : Hom (C ×C C ×C C) a b} {g : Hom (C ×C C ×C C) b c}
               → G₁ (g ∘CCC f) ≡ (G₁ g) ∘C (G₁ f)
      composeG {f = f₁ , f₂ , f₃} {g = g₁ , g₂ , g₃} 
        = trans (cong (λ X → F₁ F (g₁ ∘C f₁ ,' X)) (compose F)) (compose F)
  
  -- (1 ⊗ _) ⇒ _
  unitorL : Obj C → Functor (C ×C C) C → Functor C C
  unitorL e F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj C → Obj C
      G₀ x = F₀ F (e ,' x)
      
      G₁ : {a b : Obj C} → Hom C a b → Hom C (G₀ a) (G₀ b)
      G₁ f = F₁ F (idC C {e} ,' f)
      
      idG : {a : Obj C} → G₁ (idC C {a}) ≡ idC C {G₀ a}
      idG {a} = idF F
      composeG : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
               → G₁ ((C ∘ g) f) ≡ (C ∘ G₁ g) (G₁ f)
      composeG {f = f} {g} = trans (cong (λ X → F₁ F (X ,' g ∘C f)) (sym (idL C))) (compose F)

  -- (_ ⊗ 1) ⇒ _
  unitorR : Obj C → Functor (C ×C C) C → Functor C C
  unitorR e F = functor G₀ G₁ idG composeG
    where
      G₀ : Obj C → Obj C
      G₀ x = F₀ F (x ,' e)
      
      G₁ : {a b : Obj C} → Hom C a b → Hom C (G₀ a) (G₀ b)
      G₁ f = F₁ F (f ,' idC C {e})
      
      idG : {a : Obj C} → G₁ (idC C {a}) ≡ idC C {G₀ a}
      idG {a} = idF F
      composeG : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
               → G₁ ((C ∘ g) f) ≡ (C ∘ G₁ g) (G₁ f)
      composeG {f = f} {g} = trans (cong (λ X → F₁ F (g ∘C f ,' X)) (sym (idL C))) (compose F)

open FunctorApplication public

-------------------------------------------------------------------------------
-- Definition of Monoidal Categories
-------------------------------------------------------------------------------
record MonoidalCategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor monoidalCategory
  
  open Category C public
  
  field
    tensor : Functor (C ×C C) C -- ⊗ = \otimes
    
    unit : Obj
  
  open Functor hiding ( id )
  
  _⊗₀_ : (a b : Obj) → Obj
  _⊗₀_  a b = F₀ tensor (a ,' b)
  
  _⊗₁_ : {a b c d : Obj} → (f : Hom a b) → (g : Hom c d) → Hom (a ⊗₀ c) (b ⊗₀ d)
  _⊗₁_ f g = F₁ tensor (f ,' g)
  
  field 
    associator : NaturalIsomorphism (associatorL tensor) (associatorR tensor)
    
    left-unitor : NaturalIsomorphism (unitorL unit tensor) Id[ C ]
    
    right-unitor : NaturalIsomorphism (unitorR unit tensor) Id[ C ]
    
  open NaturalIsomorphism using ( η )
  
  α : (x y z : Obj) → Hom ((x ⊗₀ y) ⊗₀ z) (x ⊗₀ (y ⊗₀ z))
  α x y z = η associator (x , y , z)
  
  λ' : (x : Obj) → Hom (unit ⊗₀ x) x
  λ' x = η left-unitor x
  
  ρ : (x : Obj) → Hom (x ⊗₀ unit) x
  ρ x = η right-unitor x
  
  
  field
    triangle-id : (x y : Obj) → (ρ x ⊗₁ id {y}) ≡ (id {x} ⊗₁ λ' y) ∘ α x unit y
    
    pentagon-id : (w x y z : Obj) 
                → (id {w} ⊗₁ α x y z) ∘ (α w (x ⊗₀ y) z ∘ (α w x y ⊗₁ id {z})) ≡ α w x (y ⊗₀ z) ∘ α (w ⊗₀ x) y z
  
