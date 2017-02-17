
module Theory.Examples.Functor where 

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
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.NaturalTransformation.Whisker

open import Theory.Examples.Category renaming ( functorCategory to Fun )

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
        ≡⟨ propNatTransEq refl refl lemma ⟩
      Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        ≡⟨ refl ⟩
      Category.id (Fun A C) {a = [ proj₁' F ]∘[ proj₂' F ]} ∎
      where
        _∘C_ = _∘_ C
        
        lemma : η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ ≡ η Id⟨ [ proj₁' F ]∘[ proj₂' F ] ⟩
        lemma = funExt $ λ (x : Obj A) → begin 
          η ⟨ Id⟨ proj₁' F ⟩ ⟩∘ₕ⟨ Id⟨ proj₂' F ⟩ ⟩ x
            ≡⟨ refl ⟩
          η Id⟨ proj₁' F ⟩ ([ proj₂' F ]₀ x) ∘C [ proj₁' F ]₁ (η Id⟨ proj₂' F ⟩ x)
            ≡⟨ refl ⟩
          idC C ∘C [ proj₁' F ]₁ (idC B)
            ≡⟨ idR C ⟩
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
      propNatTransEq refl refl $ funExt $ λ (x : Obj A) → begin
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
  ; compose = refl
  }

rightAssocTriFunctor 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
  → Functor (C ×C D ×C E) (C ×C (D ×C E))
rightAssocTriFunctor {C = C} {D} {E} = record 
  { F₀ = assocTripleR
  ; F₁ = assocTripleR
  ; id = refl
  ; compose = refl
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
  ; compose = composeF
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
  ; compose = composeF
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
      [ J×E→K ]₁ ([ C×D→J ]₁ (Category.id (C ×C D)) ,' id E)
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

functorCompIdR : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
               → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
               → (F : Functor A B)
               → [ Id[ B ] ]∘[ F ] ≡ F
functorCompIdR F = functor-eq refl refl

functorCompIdL : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
               → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
               → (F : Functor A B)
               → [ F ]∘[ Id[ A ] ] ≡ F
functorCompIdL F = functor-eq refl refl
