
module Theory.Examples.Functor where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product renaming ( _,_ to _,'_ ; proj₁ to proj₁' ; proj₂ to proj₂' )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Utilities
open import Theory.Triple
open import Theory.Category
open import Theory.Functor

-------------------------------------------------------------------------------
-- Tri-Functors that map Triples into associated tuples/products
-------------------------------------------------------------------------------
leftAssocTriFunctor 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → Functor (C ×C D ×C E) ((C ×C D) ×C E)
leftAssocTriFunctor {C = C} {D} {E} = record 
  { F₀ = assocTripleL
  ; F₁ = assocTripleL
  ; id = refl
  ; dist = refl
  }

rightAssocTriFunctor 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → Functor (C ×C D ×C E) (C ×C (D ×C E))
rightAssocTriFunctor {C = C} {D} {E} = record 
  { F₀ = assocTripleR
  ; F₁ = assocTripleR
  ; id = refl
  ; dist = refl
  }

A×B×C→[A×B]×C = leftAssocTriFunctor
A×B×C→A×[B×C] = rightAssocTriFunctor

-------------------------------------------------------------------------------
-- Creating a Tri-Functor from two Bi-Functors (Variant 1: C × (D × E))
-------------------------------------------------------------------------------
biFunctor→triFunctor₁ 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓJ₀ ℓJ₁ ℓK₀ ℓK₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → {J : Category {ℓJ₀} {ℓJ₁}} {K : Category {ℓK₀} {ℓK₁}}
  → Functor (C ×C J) K → Functor (D ×C E) J → Functor (C ×C (D ×C E)) K
biFunctor→triFunctor₁ {C = C} {D} {E} {J} {K} C×J→K D×E→J = record 
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = idF 
  ; dist = distF
  } where
    open Category
    
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
    
    _∘K_ = _∘_ K
    _∘C_ = _∘_ C
    _∘J_ = _∘_ J
    _∘CJ_ = _∘_ (C ×C J)
    _∘CDE_ = _∘_ (C ×C (D ×C E))
    _∘DE_ = _∘_ (D ×C E)
    
    distF : {a b c : Obj (C ×C (D ×C E))} {f : Hom (C ×C (D ×C E)) a b} {g : Hom (C ×C (D ×C E)) b c} 
         → F₁ (((C ×C (D ×C E)) ∘ g) f) ≡ (K ∘ F₁ g) (F₁ f)
    distF {f = fC ,' fDE} {g = gC ,' gDE} = begin
      F₁ ((gC ,' gDE) ∘CDE (fC ,' fDE))
        ≡⟨ refl ⟩
      [ C×J→K ]₁ (gC ∘C fC ,' [ D×E→J ]₁ (gDE ∘DE fDE))
        ≡⟨ cong (λ X → [ C×J→K ]₁ (gC ∘C fC ,' X)) (Functor.dist D×E→J) ⟩ 
      [ C×J→K ]₁ (gC ∘C fC ,' [ D×E→J ]₁ gDE ∘J [ D×E→J ]₁ fDE)
        ≡⟨ refl ⟩ 
      [ C×J→K ]₁ ((gC ,' [ D×E→J ]₁ gDE) ∘CJ (fC ,' [ D×E→J ]₁ fDE))
        ≡⟨ Functor.dist C×J→K ⟩ 
      ([ C×J→K ]₁ (gC ,' [ D×E→J ]₁ gDE)) ∘K ([ C×J→K ]₁ (fC ,' [ D×E→J ]₁ fDE))
        ≡⟨ refl ⟩
      (F₁ (gC ,' gDE)) ∘K (F₁ (fC ,' fDE)) ∎

-------------------------------------------------------------------------------
-- Creating a Tri-Functor from two Bi-Functors (Variant 2: (C × D) × E)
-------------------------------------------------------------------------------
biFunctor→triFunctor₂
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓJ₀ ℓJ₁ ℓK₀ ℓK₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → {J : Category {ℓJ₀} {ℓJ₁}} {K : Category {ℓK₀} {ℓK₁}}
  → Functor (C ×C D) J → Functor (J ×C E) K → Functor ((C ×C D) ×C E) K
biFunctor→triFunctor₂ {C = C} {D} {E} {J} {K} C×D→J J×E→K = record 
  { F₀ = F₀
  ; F₁ = F₁ 
  ; id = idF 
  ; dist = distF
  } where
    open Category
    
    F₀ : Obj ((C ×C D) ×C E) → Obj K
    F₀ (c×d ,' e) = [ J×E→K ]₀ ([ C×D→J ]₀ c×d ,' e)

    F₁ : {a b : Obj ((C ×C D) ×C E)} → Hom ((C ×C D) ×C E) a b → Hom K (F₀ a) (F₀ b)
    F₁ (c×d ,' e) = [ J×E→K ]₁ ([ C×D→J ]₁ c×d ,' e)
    
    idF : {a : Obj ((C ×C D) ×C E)} 
        → F₁ {a} {a} (id ((C ×C D) ×C E)) ≡ id K
    idF {a} = begin 
      F₁ (id ((C ×C D) ×C E)) 
        ≡⟨ refl ⟩ 
      [ J×E→K ]₁ ([ C×D→J ]₁ id (C ×C D) ,' id E)
        ≡⟨ cong (λ X → [ J×E→K ]₁ (X ,' id E)) (Functor.id C×D→J) ⟩ 
      [ J×E→K ]₁ (id J ,' id E)
        ≡⟨ Functor.id J×E→K ⟩ 
      id K ∎
    
    _∘K_ = _∘_ K
    _∘E_ = _∘_ E
    _∘J_ = _∘_ J
    _∘JE_ = _∘_ (J ×C E)
    _∘CDE_ = _∘_ ((C ×C D) ×C E)
    _∘CD_ = _∘_ (C ×C D)
    
    distF : {a b c : Obj ((C ×C D) ×C E)} {f : Hom ((C ×C D) ×C E) a b} {g : Hom ((C ×C D) ×C E) b c} 
         → F₁ (g ∘CDE f) ≡ (F₁ g) ∘K (F₁ f)
    distF {f = fCD ,' fE} {g = gCD ,' gE} = begin
      F₁ ((gCD ,' gE) ∘CDE (fCD ,' fE))
        ≡⟨ refl ⟩
      [ J×E→K ]₁ ([ C×D→J ]₁ (gCD ∘CD fCD) ,' gE ∘E fE)
        ≡⟨ cong (λ X → [ J×E→K ]₁ (X ,' gE ∘E fE)) (Functor.dist C×D→J) ⟩ 
      [ J×E→K ]₁ ([ C×D→J ]₁ gCD ∘J [ C×D→J ]₁ fCD ,' gE ∘E  fE)
        ≡⟨ refl ⟩ 
      [ J×E→K ]₁ (([ C×D→J ]₁ gCD ,' gE) ∘JE ([ C×D→J ]₁ fCD ,' fE))
        ≡⟨ Functor.dist J×E→K ⟩ 
      ([ J×E→K ]₁ ([ C×D→J ]₁ gCD ,' gE)) ∘K ([ J×E→K ]₁ ([ C×D→J ]₁ fCD ,' fE))
        ≡⟨ refl ⟩
      (F₁ (gCD ,' gE)) ∘K (F₁ (fCD ,' fE)) ∎
