 
module Theory.MonoidalCategory where

open import Level renaming ( zero to lzero ; suc to lsuc )
open import Data.Product renaming ( _,_ to _,'_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

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
  associatorL F = functor F₀' F₁' id' compose'
    where
      F₀' : Obj (C ×C C ×C C) → Obj C
      F₀' (a , b , c) = F₀ F (F₀ F (a ,' b) ,' c)
      
      F₁' : {a b : Obj (C ×C C ×C C)} → Hom (C ×C C ×C C) a b → Hom C (F₀' a) (F₀' b)
      F₁' (f , g , h) = F₁ F (F₁ F (f ,' g) ,' h)
      
      id' : {a : Obj (C ×C C ×C C)} → F₁' {a} {a} (idC (C ×C C ×C C)) ≡ idC C
      id' = trans (cong (λ X → F₁ F (X ,' idC C)) (idF F)) (idF F)
      
      compose' : {a b c : Obj (C ×C C ×C C)} 
               → {f : Hom (C ×C C ×C C) a b} {g : Hom (C ×C C ×C C) b c}
               → F₁' (g ∘CCC f) ≡ (F₁' g) ∘C (F₁' f)
      compose' {f = f} {g} = {!!}
  
  -- (_ ⊗ (_ ⊗ _)) ⇒ _
  associatorR : Functor (C ×C C) C → Functor (C ×C C ×C C) C 
  associatorR F = functor F₀' F₁' id' compose'
    where
      F₀' : Obj (C ×C C ×C C) → Obj C
      F₀' (a , b , c) = F₀ F (a ,' F₀ F (b ,' c))
      
      F₁' : {a b : Obj (C ×C C ×C C)} → Hom (C ×C C ×C C) a b → Hom C (F₀' a) (F₀' b)
      F₁' (f , g , h) = F₁ F (f ,' F₁ F (g ,' h))
      
      id' : {a : Obj (C ×C C ×C C)} → F₁' {a} {a} (idC (C ×C C ×C C)) ≡ idC C
      id' = trans (cong (λ X → F₁ F (idC C ,' X)) (idF F)) (idF F)
      
      compose' : {a b c : Obj (C ×C C ×C C)} 
               → {f : Hom (C ×C C ×C C) a b} {g : Hom (C ×C C ×C C) b c}
               → F₁' (g ∘CCC f) ≡ (F₁' g) ∘C (F₁' f)
      compose' = {!!}

-------------------------------------------------------------------------------
-- Definition of Monoidal Categories
-------------------------------------------------------------------------------
record MonoidalCategory {ℓ₀ ℓ₁ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor monoidalCategory
  field
    C : Category {ℓ₀} {ℓ₁}

  open Category C
  
  field
    tensor : Functor (C ×C C) C -- ⊗ = \otimes
    
    unit : Obj

  open FunctorApplication
  
  field 
    associator : NaturalIsomorphism (associatorL tensor) (associatorR tensor)

    {-
    Obj : Set ℓ₀
    Hom : Obj → Obj → Set ℓ₁
    
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id : ∀ {a} → Hom a a
    
    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    idR : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    idL : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f
-}
