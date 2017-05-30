
open import Level

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Functor.Definition

module Theory.Functor.Association where

-------------------------------------------------------------------------------
-- Tri-Functors that map Triples into associated tuples/products
-------------------------------------------------------------------------------
module Triple {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
              {C : Category {ℓC₀} {ℓC₁}} 
              {D : Category {ℓD₀} {ℓD₁}}
              {E : Category {ℓE₀} {ℓE₁}} where
  open import Theory.Triple

  assocFunctorL : Functor (C ×C D ×C E) ((C ×C D) ×C E)
  assocFunctorL = functor assocTripleL assocTripleL refl refl
  
  assocFunctorR : Functor (C ×C D ×C E) (C ×C (D ×C E))
  assocFunctorR = functor assocTripleR assocTripleR refl refl
  
  unassocFunctorR : Functor (C ×C (D ×C E)) (C ×C D ×C E)
  unassocFunctorR = functor unassocTripleR unassocTripleR refl refl
  
  unassocFunctorL : Functor ((C ×C D) ×C E) (C ×C D ×C E)
  unassocFunctorL = functor unassocTripleL unassocTripleL refl refl

-------------------------------------------------------------------------------
-- Creating a Tri-Functors from two Bi-Functors
-------------------------------------------------------------------------------
module BiFunctor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓJ₀ ℓJ₁ ℓK₀ ℓK₁ : Level} 
                 {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
                 {J : Category {ℓJ₀} {ℓJ₁}} {K : Category {ℓK₀} {ℓK₁}} where
  open import Data.Product
  open Category

  private
    _∘K_ = _∘_ K
    _∘C_ = _∘_ C
    _∘E_ = _∘_ E
    _∘J_ = _∘_ J
    _∘CD_ = _∘_ (C ×C D)
    _∘CJ_ = _∘_ (C ×C J)
    _∘JE_ = _∘_ (J ×C E)
    _∘DE_ = _∘_ (D ×C E)
  
  biAssocFunctorR : Functor (C ×C J) K → Functor (D ×C E) J → Functor (C ×C (D ×C E)) K
  biAssocFunctorR C×J→K D×E→J = functor F₀ F₁ idF composeF
    where
      F₀ : Obj (C ×C (D ×C E)) → Obj K
      F₀ (c , d×e) = [ C×J→K ]₀ (c , [ D×E→J ]₀ d×e)
  
      F₁ : {a b : Obj (C ×C (D ×C E))} → Hom (C ×C (D ×C E)) a b → Hom K (F₀ a) (F₀ b)
      F₁ (c , d×e) = [ C×J→K ]₁ (c , [ D×E→J ]₁ d×e)
      
      idF : {a : Obj (C ×C (D ×C E))} 
          → F₁ {a} {a} (id (C ×C (D ×C E))) ≡ id K
      idF {a} = begin 
        F₁ (id (C ×C (D ×C E))) 
          ≡⟨ refl ⟩ 
        [ C×J→K ]₁ (id C , [ D×E→J ]₁ (id (D ×C E)))
          ≡⟨ cong (λ X → [ C×J→K ]₁ (id C , X)) (Functor.id D×E→J) ⟩ 
        [ C×J→K ]₁ (id C , id J)
          ≡⟨ Functor.id C×J→K ⟩ 
        id K ∎
      
      private 
        _∘CDE_ = _∘_ (C ×C (D ×C E))
      
      composeF : {a b c : Obj (C ×C (D ×C E))} {f : Hom (C ×C (D ×C E)) a b} {g : Hom (C ×C (D ×C E)) b c} 
               → F₁ (((C ×C (D ×C E)) ∘ g) f) ≡ (K ∘ F₁ g) (F₁ f)
      composeF {f = fC , fDE} {g = gC , gDE} = begin
        F₁ ((gC , gDE) ∘CDE (fC , fDE))
          ≡⟨ refl ⟩
        [ C×J→K ]₁ (gC ∘C fC , [ D×E→J ]₁ (gDE ∘DE fDE))
          ≡⟨ cong (λ X → [ C×J→K ]₁ (gC ∘C fC , X)) (Functor.compose D×E→J) ⟩ 
        [ C×J→K ]₁ (gC ∘C fC , [ D×E→J ]₁ gDE ∘J [ D×E→J ]₁ fDE)
          ≡⟨ refl ⟩ 
        [ C×J→K ]₁ ((gC , [ D×E→J ]₁ gDE) ∘CJ (fC , [ D×E→J ]₁ fDE))
          ≡⟨ Functor.compose C×J→K ⟩ 
        ([ C×J→K ]₁ (gC , [ D×E→J ]₁ gDE)) ∘K ([ C×J→K ]₁ (fC , [ D×E→J ]₁ fDE))
          ≡⟨ refl ⟩
        (F₁ (gC , gDE)) ∘K (F₁ (fC , fDE)) ∎

  biAssocFunctorL : Functor (C ×C D) J → Functor (J ×C E) K → Functor ((C ×C D) ×C E) K
  biAssocFunctorL C×D→J J×E→K = functor F₀ F₁ idF composeF
    where
      F₀ : Obj ((C ×C D) ×C E) → Obj K
      F₀ (c×d , e) = [ J×E→K ]₀ ([ C×D→J ]₀ c×d , e)
  
      F₁ : {a b : Obj ((C ×C D) ×C E)} → Hom ((C ×C D) ×C E) a b → Hom K (F₀ a) (F₀ b)
      F₁ (c×d , e) = [ J×E→K ]₁ ([ C×D→J ]₁ c×d , e)
      
      idF : {a : Obj ((C ×C D) ×C E)} 
          → F₁ {a} {a} (id ((C ×C D) ×C E)) ≡ id K
      idF {a} = begin 
        F₁ (id ((C ×C D) ×C E)) 
          ≡⟨ refl ⟩ 
        [ J×E→K ]₁ ([ C×D→J ]₁ (Category.id (C ×C D)) , id E)
          ≡⟨ cong (λ X → [ J×E→K ]₁ (X , id E)) (Functor.id C×D→J) ⟩ 
        [ J×E→K ]₁ (id J , id E)
          ≡⟨ Functor.id J×E→K ⟩ 
        id K ∎
      
      private 
        _∘CDE_ = _∘_ ((C ×C D) ×C E)
      
      composeF : {a b c : Obj ((C ×C D) ×C E)} {f : Hom ((C ×C D) ×C E) a b} {g : Hom ((C ×C D) ×C E) b c} 
               → F₁ (g ∘CDE f) ≡ (F₁ g) ∘K (F₁ f)
      composeF {f = fCD , fE} {g = gCD , gE} = begin
        F₁ ((gCD , gE) ∘CDE (fCD , fE))
          ≡⟨ refl ⟩
        [ J×E→K ]₁ ([ C×D→J ]₁ (gCD ∘CD fCD) , gE ∘E fE)
          ≡⟨ cong (λ X → [ J×E→K ]₁ (X , gE ∘E fE)) (Functor.compose C×D→J) ⟩ 
        [ J×E→K ]₁ ([ C×D→J ]₁ gCD ∘J [ C×D→J ]₁ fCD , gE ∘E  fE)
          ≡⟨ refl ⟩ 
        [ J×E→K ]₁ (([ C×D→J ]₁ gCD , gE) ∘JE ([ C×D→J ]₁ fCD , fE))
          ≡⟨ Functor.compose J×E→K ⟩ 
        ([ J×E→K ]₁ ([ C×D→J ]₁ gCD , gE)) ∘K ([ J×E→K ]₁ ([ C×D→J ]₁ fCD , fE))
          ≡⟨ refl ⟩
        (F₁ (gCD , gE)) ∘K (F₁ (fCD , fE)) ∎

-------------------------------------------------------------------------------
-- Associator functors
-------------------------------------------------------------------------------
module Associator {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where
  open Triple
  open BiFunctor
  open import Theory.Functor.Composition
  
  -- ((_ ⊗ _) ⊗ _) ⇒ _
  leftAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C
  leftAssociator F = [ biAssocFunctorL F F ]∘[ assocFunctorL ]
  
  -- (_ ⊗ (_ ⊗ _)) ⇒ _
  rightAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C 
  rightAssociator F = [ biAssocFunctorR F F ]∘[ assocFunctorR ]
 
