
module Theory.Functor.Examples where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product renaming ( _,_ to _,'_ ; proj₁ to proj₁' ; proj₂ to proj₂' )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( cong ; subst ; subst₂ ; sym ; trans )
open ≡-Reasoning 

-- Local
open import Utilities
open import Extensionality
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Whisker

open import Theory.Category.Examples renaming ( functorCategory to Fun )

-------------------------------------------------------------------------------
-- Horizontal composition functor for natural transformations.
-------------------------------------------------------------------------------
natTransCompositionHorzFunctor 
  : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ : Level} 
  → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} {C : Category {ℓC₀} {ℓC₁}} 
  → Functor (Fun B C ×C Fun A B) (Fun A C)
natTransCompositionHorzFunctor {A = A} {B} {C} = record 
  { F₀ = F₀ 
  ; F₁ = F₁
  ; id = λ {F} → id {F}
  ; compose = λ {F} {G} {H} {α} {β} → compose {F} {G} {H} {α} {β} 
  } where  
    open Category renaming ( id to idC )
    open NaturalTransformation
    
    F₀ : Obj (Fun B C ×C Fun A B) → Obj (Fun A C)
    F₀ (G ,' F) = [ G ]∘[ F ]
    
    F₁ : {F G : Obj (Fun B C ×C Fun A B)} 
       → Hom (Fun B C ×C Fun A B) F G → Hom (Fun A C) (F₀ F) (F₀ G)
    F₁ (α ,' β) = ⟨ α ⟩∘ₕ⟨ β ⟩
    
    id : {F : Obj (Fun B C ×C Fun A B)} 
       → F₁ {F = F} {G = F} (idC (Fun B C ×C Fun A B)) ≡ idC (Fun A C)
    id {F} = begin 
      F₁ {F = F} {G = F} (idC (Fun B C ×C Fun A B)) 
        ≡⟨ refl ⟩
      ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ 
        ≡⟨ natural-transformation-eq lemma ⟩
      Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        ≡⟨ refl ⟩
      Category.id (Fun A C) {a = [ proj₁' F ]∘[ proj₂' F ]} ∎
      where
        _∘C_ = _∘_ C
        
        lemma : η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ ≡ η Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        lemma = fun-ext $ λ (x : Obj A) → begin 
          η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ x
            ≡⟨ refl ⟩
          η Id⟨ proj₁' F ⟩ ([ proj₂' F ]₀ x) ∘C [ proj₁' F ]₁ (η Id⟨ proj₂' F ⟩ x)
            ≡⟨ refl ⟩
          idC C ∘C [ proj₁' F ]₁ (idC B)
            ≡⟨ right-id C ⟩
          [ proj₁' F ]₁ (idC B)
            ≡⟨ Functor.id (proj₁' F) ⟩
          idC C
            ≡⟨ refl ⟩
          η Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩ x ∎
        
    compose : {F G H : Obj (Fun B C ×C Fun A B)}
         → {α : Hom (Fun B C ×C Fun A B) F G}
         → {β : Hom (Fun B C ×C Fun A B) G H}
         → F₁ ( ⟨ proj₁' β ⟩∘ᵥ⟨ proj₁' α ⟩ ,' ⟨ proj₂' β ⟩∘ᵥ⟨ proj₂' α ⟩ ) ≡ ⟨ F₁ β ⟩∘ᵥ⟨ F₁ α ⟩
    compose {F ,' F'} {G ,' G'} {H ,' H'} {α = α₁ ,' α₂} {β = β₁ ,' β₂} = 
      natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
        η ⟨ ⟨ β₁ ⟩∘ᵥ⟨ α₁ ⟩ ⟩∘ₕ⟨ ⟨ β₂ ⟩∘ᵥ⟨ α₂ ⟩ ⟩ x
          ≡⟨ refl ⟩
        η ⟨ β₁ ⟩∘ᵥ⟨ α₁ ⟩ ([ H' ]₀ x) ∘C [ F ]₁ (η ⟨ β₂ ⟩∘ᵥ⟨ α₂ ⟩ x)
          ≡⟨ refl ⟩
        (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C [ F ]₁ (η β₂ x ∘B η α₂ x)
           ≡⟨ cong (λ X → (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C X) (Functor.compose F) ⟩
        (η β₁ ([ H' ]₀ x) ∘C η α₁ ([ H' ]₀ x)) ∘C ([ F ]₁ (η β₂ x) ∘C [ F ]₁ (η α₂ x))
           ≡⟨ sym (assoc C) ⟩
        η β₁ ([ H' ]₀ x) ∘C (η α₁ ([ H' ]₀ x) ∘C ([ F ]₁ (η β₂ x) ∘C [ F ]₁ (η α₂ x)))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C X) (assoc C) ⟩
        η β₁ ([ H' ]₀ x) ∘C ((η α₁ ([ H' ]₀ x) ∘C [ F ]₁ (η β₂ x)) ∘C [ F ]₁ (η α₂ x))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C (X ∘C [ F ]₁ (η α₂ x))) (sym (cong (λ X → X x) (cong η (whiskerCompositionHorzEq β₂ α₁)))) ⟩
        η β₁ ([ H' ]₀ x) ∘C (([ G ]₁ (η β₂ x) ∘C η α₁ ([ G' ]₀ x)) ∘C [ F ]₁ (η α₂ x))
          ≡⟨ cong (λ X → η β₁ ([ H' ]₀ x) ∘C X) (sym (assoc C)) ⟩
        η β₁ ([ H' ]₀ x) ∘C ([ G ]₁ (η β₂ x) ∘C (η α₁ ([ G' ]₀ x) ∘C [ F ]₁ (η α₂ x)))
          ≡⟨ assoc C ⟩
        (η β₁ ([ H' ]₀ x) ∘C [ G ]₁ (η β₂ x)) ∘C (η α₁ ([ G' ]₀ x) ∘C [ F ]₁ (η α₂ x))
           ≡⟨ refl ⟩
        η ⟨ β₁ ⟩∘ₕ⟨ β₂ ⟩ x ∘C η ⟨ α₁ ⟩∘ₕ⟨ α₂ ⟩ x
          ≡⟨ refl ⟩
        η ⟨ ⟨ β₁ ⟩∘ₕ⟨ β₂ ⟩ ⟩∘ᵥ⟨ ⟨ α₁ ⟩∘ₕ⟨ α₂ ⟩ ⟩ x ∎
      where _∘B_ = _∘_ B ; _∘C_ = _∘_ C

-------------------------------------------------------------------------------
-- Composition of identity functors
-------------------------------------------------------------------------------
functor-composition-left-id : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                            → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
                            → (F : Functor A B)
                            → [ Id[ B ] ]∘[ F ] ≡ F
functor-composition-left-id F = functor-eq refl refl

functor-composition-right-id : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
                             → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
                             → (F : Functor A B)
                             → [ F ]∘[ Id[ A ] ] ≡ F
functor-composition-right-id F = functor-eq refl refl

-------------------------------------------------------------------------------
-- Application of objects to bifunctors
-------------------------------------------------------------------------------
module BiFunctorApplication {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                            {C : Category {ℓC₀} {ℓC₁}} 
                            {D : Category {ℓD₀} {ℓD₁}}
                            {E : Category {ℓE₀} {ℓE₁}} where
  open Category
  private
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    _∘E_ = _∘_ E
  
  leftObjApply : Obj C → Functor (C ×C D) E → Functor D E
  leftObjApply x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
    where
      ObjF : Obj D → Obj E
      ObjF d = F₀ (x ,' d)
      
      HomF : {a b : Obj D} → Hom D a b → Hom E (ObjF a) (ObjF b)
      HomF f = F₁ (id C {x} ,' f)
      
      composeF : {a b c : Obj D} {f : Hom D a b} {g : Hom D b c}
               → HomF (g ∘D f) ≡ HomF g ∘E HomF f
      composeF {a} {b} {c} {f} {g} = begin
        F₁ (id C {x} ,' g ∘D f)
          ≡⟨ cong (λ X → F₁ (X ,' g ∘D f)) (sym $ left-id C) ⟩
        F₁ (id C {x} ∘C id C {x} ,' g ∘D f)
          ≡⟨ compose ⟩
        F₁ (id C {x} ,' g) ∘E F₁ (id C {x} ,' f) ∎
  
  [_,-] = leftObjApply
  
  rightObjApply : Obj D → Functor (C ×C D) E → Functor C E
  rightObjApply x (functor F₀ F₁ functor-id compose) = functor ObjF HomF functor-id composeF
    where
      ObjF : Obj C → Obj E
      ObjF c = F₀ (c ,' x)
      
      HomF : {a b : Obj C} → Hom C a b → Hom E (ObjF a) (ObjF b)
      HomF f = F₁ (f ,' id D {x})
      
      composeF : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
               → HomF (g ∘C f) ≡ HomF g ∘E HomF f
      composeF {a} {b} {c} {f} {g} = begin
        F₁ (g ∘C f ,' id D {x})
          ≡⟨ cong (λ X → F₁ (g ∘C f ,' X)) (sym $ left-id D) ⟩
        F₁ (g ∘C f ,' id D {x} ∘D id D {x})
          ≡⟨ compose ⟩
        F₁ (g ,' id D {x}) ∘E F₁ (f ,' id D {x}) ∎
  
  [-,_] = rightObjApply

-------------------------------------------------------------------------------
-- Tri-Functors that map Triples into associated tuples/products
-------------------------------------------------------------------------------

module TripleAssociation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
                         {C : Category {ℓC₀} {ℓC₁}} 
                         {D : Category {ℓD₀} {ℓD₁}}
                         {E : Category {ℓE₀} {ℓE₁}} where
       
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
module BiFunctorAssociation {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓJ₀ ℓJ₁ ℓK₀ ℓK₁ : Level} 
                            {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
                            {J : Category {ℓJ₀} {ℓJ₁}} {K : Category {ℓK₀} {ℓK₁}} where
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
      F₀ (c ,' d×e) = [ C×J→K ]₀ (c ,' [ D×E→J ]₀ d×e)
  
      F₁ : {a b : Obj (C ×C (D ×C E))} → Hom (C ×C (D ×C E)) a b → Hom K (F₀ a) (F₀ b)
      F₁ (c ,' d×e) = [ C×J→K ]₁ (c ,' [ D×E→J ]₁ d×e)
      
      idF : {a : Obj (C ×C (D ×C E))} 
          → F₁ {a} {a} (id (C ×C (D ×C E))) ≡ id K
      idF {a} = begin 
        F₁ (id (C ×C (D ×C E))) 
          ≡⟨ refl ⟩ 
        [ C×J→K ]₁ (id C ,' [ D×E→J ]₁ (id (D ×C E)))
          ≡⟨ cong (λ X → [ C×J→K ]₁ (id C ,' X)) (Functor.id D×E→J) ⟩ 
        [ C×J→K ]₁ (id C ,' id J)
          ≡⟨ Functor.id C×J→K ⟩ 
        id K ∎
      
      private 
        _∘CDE_ = _∘_ (C ×C (D ×C E))
      
      composeF : {a b c : Obj (C ×C (D ×C E))} {f : Hom (C ×C (D ×C E)) a b} {g : Hom (C ×C (D ×C E)) b c} 
               → F₁ (((C ×C (D ×C E)) ∘ g) f) ≡ (K ∘ F₁ g) (F₁ f)
      composeF {f = fC ,' fDE} {g = gC ,' gDE} = begin
        F₁ ((gC ,' gDE) ∘CDE (fC ,' fDE))
          ≡⟨ refl ⟩
        [ C×J→K ]₁ (gC ∘C fC ,' [ D×E→J ]₁ (gDE ∘DE fDE))
          ≡⟨ cong (λ X → [ C×J→K ]₁ (gC ∘C fC ,' X)) (Functor.compose D×E→J) ⟩ 
        [ C×J→K ]₁ (gC ∘C fC ,' [ D×E→J ]₁ gDE ∘J [ D×E→J ]₁ fDE)
          ≡⟨ refl ⟩ 
        [ C×J→K ]₁ ((gC ,' [ D×E→J ]₁ gDE) ∘CJ (fC ,' [ D×E→J ]₁ fDE))
          ≡⟨ Functor.compose C×J→K ⟩ 
        ([ C×J→K ]₁ (gC ,' [ D×E→J ]₁ gDE)) ∘K ([ C×J→K ]₁ (fC ,' [ D×E→J ]₁ fDE))
          ≡⟨ refl ⟩
        (F₁ (gC ,' gDE)) ∘K (F₁ (fC ,' fDE)) ∎

  biAssocFunctorL : Functor (C ×C D) J → Functor (J ×C E) K → Functor ((C ×C D) ×C E) K
  biAssocFunctorL C×D→J J×E→K = functor F₀ F₁ idF composeF
    where
      F₀ : Obj ((C ×C D) ×C E) → Obj K
      F₀ (c×d ,' e) = [ J×E→K ]₀ ([ C×D→J ]₀ c×d ,' e)
  
      F₁ : {a b : Obj ((C ×C D) ×C E)} → Hom ((C ×C D) ×C E) a b → Hom K (F₀ a) (F₀ b)
      F₁ (c×d ,' e) = [ J×E→K ]₁ ([ C×D→J ]₁ c×d ,' e)
      
      idF : {a : Obj ((C ×C D) ×C E)} 
          → F₁ {a} {a} (id ((C ×C D) ×C E)) ≡ id K
      idF {a} = begin 
        F₁ (id ((C ×C D) ×C E)) 
          ≡⟨ refl ⟩ 
        [ J×E→K ]₁ ([ C×D→J ]₁ (Category.id (C ×C D)) ,' id E)
          ≡⟨ cong (λ X → [ J×E→K ]₁ (X ,' id E)) (Functor.id C×D→J) ⟩ 
        [ J×E→K ]₁ (id J ,' id E)
          ≡⟨ Functor.id J×E→K ⟩ 
        id K ∎
      
      private 
        _∘CDE_ = _∘_ ((C ×C D) ×C E)
      
      composeF : {a b c : Obj ((C ×C D) ×C E)} {f : Hom ((C ×C D) ×C E) a b} {g : Hom ((C ×C D) ×C E) b c} 
               → F₁ (g ∘CDE f) ≡ (F₁ g) ∘K (F₁ f)
      composeF {f = fCD ,' fE} {g = gCD ,' gE} = begin
        F₁ ((gCD ,' gE) ∘CDE (fCD ,' fE))
          ≡⟨ refl ⟩
        [ J×E→K ]₁ ([ C×D→J ]₁ (gCD ∘CD fCD) ,' gE ∘E fE)
          ≡⟨ cong (λ X → [ J×E→K ]₁ (X ,' gE ∘E fE)) (Functor.compose C×D→J) ⟩ 
        [ J×E→K ]₁ ([ C×D→J ]₁ gCD ∘J [ C×D→J ]₁ fCD ,' gE ∘E  fE)
          ≡⟨ refl ⟩ 
        [ J×E→K ]₁ (([ C×D→J ]₁ gCD ,' gE) ∘JE ([ C×D→J ]₁ fCD ,' fE))
          ≡⟨ Functor.compose J×E→K ⟩ 
        ([ J×E→K ]₁ ([ C×D→J ]₁ gCD ,' gE)) ∘K ([ J×E→K ]₁ ([ C×D→J ]₁ fCD ,' fE))
          ≡⟨ refl ⟩
        (F₁ (gCD ,' gE)) ∘K (F₁ (fCD ,' fE)) ∎

-------------------------------------------------------------------------------
-- Associator functors
-------------------------------------------------------------------------------
module Associator {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where
  open TripleAssociation
  open BiFunctorAssociation
  
  -- ((_ ⊗ _) ⊗ _) ⇒ _
  leftAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C
  leftAssociator F = [ biAssocFunctorL F F ]∘[ assocFunctorL ]
  
  -- (_ ⊗ (_ ⊗ _)) ⇒ _
  rightAssociator : Functor (C ×C C) C → Functor (C ×C C ×C C) C 
  rightAssociator F = [ biAssocFunctorR F F ]∘[ assocFunctorR ]
