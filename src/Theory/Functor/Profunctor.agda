
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat renaming (setCategory to SetCat)
open import Theory.Functor.Definition
open import Theory.Functor.Examples.HomFunctor
open import Theory.End.Definition
open import Theory.End.Wedge

module Theory.Functor.Profunctor where

open Category
open Functor

Profunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
           → (ℓSet : Level) 
           → (C : Category {ℓC₀} {ℓC₁})
           → (D : Category {ℓD₀} {ℓD₁}) 
           → Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ suc ℓSet)
Profunctor ℓSet C D = Functor (D op ×C C) (SetCat {ℓSet})

heteromorphisms : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {ℓSet : Level} 
                → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
                → Profunctor ℓSet C D
                → (d : Obj D) → (c : Obj C) → Set ℓSet
heteromorphisms H d c = [ H ]₀ (d , c)


inducedProfunctor[1,F] : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                       → (F : Functor C D)
                       → (ℓSet : Level)
                       → Profunctor (ℓSet ⊔ ℓD₀ ⊔ ℓD₁) C D
inducedProfunctor[1,F] {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {C} {D} F ℓSet = (functor IF₀ IF₁ IF-id IF-compose)
  where
    _∘D×C_ = _∘_ (D op ×C C)
    _∘Set_ = _∘_ (SetCat {ℓSet ⊔ ℓD₀ ⊔ ℓD₁})
    _∘D_ = _∘_ (D op)
    _∘C_ = _∘_ C
    
    IF₀ : Obj ((D op) ×C C) → Obj (SetCat {ℓSet ⊔ ℓD₀ ⊔ ℓD₁})
    IF₀ (d , c) = [ homFunctor ℓSet D ]₀ (d , [ F ]₀ c)
    
    IF₁ : {a b : Obj ((D op) ×C C)} → Hom ((D op) ×C C) a b → Hom SetCat (IF₀ a) (IF₀ b)
    IF₁ (f' , f) = [ homFunctor ℓSet D ]₁ (f' , ([ F ]₁ f))
    
    abstract
      IF-id : {a : Obj ((D op) ×C C)} → IF₁ {a} {a} (id ((D op) ×C C)) ≡ id SetCat
      IF-id {d , c} = begin
        IF₁ {d , c} {d , c} (id ((D op) ×C C)) 
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ (id (D op) , [ F ]₁ (id C)) 
          ≡⟨ cong (λ X → [ homFunctor ℓSet D ]₁ (id (D op) , X)) (Functor.id F) ⟩
        [ homFunctor ℓSet D ]₁ (id (D op) , id D) 
          ≡⟨ Functor.id (homFunctor ℓSet D) ⟩
        id SetCat ∎
    
    abstract
      IF-compose : {a b c : Obj ((D op) ×C C)}
                 → {f : Hom ((D op) ×C C) a b} {g : Hom ((D op) ×C C) b c}
                 → IF₁ (g ∘D×C f) ≡ IF₁ g ∘Set IF₁ f
      IF-compose {a} {b} {c} {f' , f} {g' , g} = begin
        IF₁ ((g' , g) ∘D×C (f' , f)) 
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ ((g' ∘D f') , ([ F ]₁ (g ∘C f)))
          ≡⟨⟩
        (λ h → lift (((g' ∘D f') ∘D lower h) ∘D ([ F ]₁ (g ∘C f))))
          ≡⟨ fun-ext (λ h → cong (λ X → lift (((g' ∘D f') ∘D lower h) ∘D X)) (Functor.compose F)) ⟩
        (λ h → lift (((g' ∘D f') ∘D lower h) ∘D ([ F ]₁ f ∘D [ F ]₁ g)))
          ≡⟨ fun-ext (λ h → cong lift (sym $ assoc D)) ⟩
        (λ h → lift ((((g' ∘D f') ∘D lower h) ∘D [ F ]₁ f) ∘D [ F ]₁ g))
          ≡⟨ fun-ext (λ h → cong (λ X → lift ((X ∘D [ F ]₁ f) ∘D [ F ]₁ g)) (assoc D)) ⟩
        (λ h → lift (((g' ∘D (f' ∘D lower h)) ∘D [ F ]₁ f) ∘D [ F ]₁ g))
          ≡⟨ fun-ext (λ h → cong (λ X → lift (X ∘D [ F ]₁ g)) (assoc D)) ⟩
        (λ h → lift ((g' ∘D ((f' ∘D lower h) ∘D [ F ]₁ f)) ∘D [ F ]₁ g))
          ≡⟨⟩
        (λ h → lift ((g' ∘D lower {ℓ = ℓSet ⊔ ℓD₁ ⊔ ℓD₀} h) ∘D [ F ]₁ g)) ∘Set (λ h → lift ((f' ∘D lower h) ∘D [ F ]₁ f))
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ (g' , [ F ]₁ g) ∘Set [ homFunctor ℓSet D ]₁ (f' , [ F ]₁ f)
          ≡⟨⟩
        IF₁ (g' , g) ∘Set IF₁ (f' , f) ∎

idProfunctor : {ℓC₀ ℓC₁ : Level} → (ℓSet : Level)
             → {C : Category {ℓC₀} {ℓC₁}} → Profunctor (ℓSet ⊔ ℓC₀ ⊔ ℓC₁) C C
idProfunctor {ℓC₀} {ℓC₁} ℓSet {C} = (homFunctor ℓSet C)

inducedProfunctor[F,1] : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                       → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                       → (F : Functor C D)
                       → (ℓSet : Level)
                       → Profunctor (ℓSet ⊔ ℓD₀ ⊔ ℓD₁) D C
inducedProfunctor[F,1] {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {C} {D} F ℓSet = (functor IF₀ IF₁ IF-id IF-compose)
  where
    _∘C×D_ = _∘_ (C op ×C D)
    _∘Set_ = _∘_ (SetCat {ℓSet ⊔ ℓD₀ ⊔ ℓD₁})
    _∘D_ = _∘_ D
    _∘C_ = _∘_ (C op)
    
    IF₀ : Obj ((C op) ×C D) → Obj (SetCat {ℓSet ⊔ ℓD₀ ⊔ ℓD₁})
    IF₀ (c , d) = [ homFunctor ℓSet D ]₀ (([ F ]₀ c) , d)
    
    IF₁ : {a b : Obj ((C op) ×C D)} → Hom ((C op) ×C D) a b → Hom SetCat (IF₀ a) (IF₀ b)
    IF₁ (f' , f) = [ homFunctor ℓSet D ]₁ (([ F ]₁ f') , f)
    
    abstract
      IF-id : {a : Obj ((C op) ×C D)} → IF₁ {a} {a} (id ((C op) ×C D)) ≡ id SetCat
      IF-id {c , d} = begin
        IF₁ {c , d} {c , d} (id ((C op) ×C D)) 
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ ([ F ]₁ (id (C op)) , (id D)) 
          ≡⟨ cong (λ X → [ homFunctor ℓSet D ]₁ (X , id D)) (Functor.id F) ⟩
        [ homFunctor ℓSet D ]₁ (id (D op) , id D) 
          ≡⟨ Functor.id (homFunctor ℓSet D) ⟩
        id SetCat ∎
    
    abstract
      IF-compose : {a b c : Obj ((C op) ×C D)}
                 → {f : Hom ((C op) ×C D) a b} {g : Hom ((C op) ×C D) b c}
                 → IF₁ (g ∘C×D f) ≡ IF₁ g ∘Set IF₁ f
      IF-compose {a} {b} {c} {f' , f} {g' , g} = begin
        IF₁ ((g' , g) ∘C×D (f' , f)) 
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ ([ F ]₁ (g' ∘C f') , (g ∘D f))
          ≡⟨⟩
        (λ h → lift ((g ∘D f) ∘D (lower h ∘D [ F ]₁ (g' ∘C f'))))
          ≡⟨ cong (λ X → (λ h → lift ((g ∘D f) ∘D (lower h ∘D X)))) (Functor.compose F) ⟩
        (λ h → lift ((g ∘D f) ∘D (lower h ∘D ([ F ]₁ f' ∘D [ F ]₁ g'))))
          ≡⟨ fun-ext (λ h → cong (λ X → lift ((g ∘D f) ∘D X)) (assoc D)) ⟩
        (λ h → lift ((g ∘D f) ∘D ((lower h ∘D [ F ]₁ f') ∘D [ F ]₁ g')))
          ≡⟨ fun-ext (λ h → cong lift (assoc D)) ⟩
        (λ h → lift (((g ∘D f) ∘D (lower h ∘D [ F ]₁ f')) ∘D [ F ]₁ g'))
          ≡⟨ fun-ext (λ h → cong (λ X → lift (X ∘D [ F ]₁ g')) (sym $ assoc D)) ⟩
        (λ h → lift ((g ∘D (f ∘D (lower h ∘D [ F ]₁ f'))) ∘D [ F ]₁ g'))
          ≡⟨ fun-ext (λ h → cong lift (sym $ assoc D)) ⟩
        (λ h → lift (g ∘D ((f ∘D (lower h ∘D [ F ]₁ f')) ∘D [ F ]₁ g')))
          ≡⟨⟩
        (λ h → lift (g ∘D (lower {ℓ = ℓSet ⊔ ℓD₁ ⊔ ℓD₀} h ∘D [ F ]₁ g'))) ∘Set (λ h → lift (f ∘D (lower h ∘D [ F ]₁ f')))
          ≡⟨⟩
        [ homFunctor ℓSet D ]₁ (([ F ]₁ g') , g) ∘Set [ homFunctor ℓSet D ]₁ (([ F ]₁ f') , f)
          ≡⟨⟩
        IF₁ (g' , g) ∘Set IF₁ (f' , f) ∎

composeProfunctorCoendFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} (ℓSet : Level)
                              → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
                              → (c : Obj C) (e : Obj E)
                              → Profunctor ℓSet C D → Profunctor ℓSet D E 
                              → Functor (D op ×C D) (SetCat {ℓSet})
composeProfunctorCoendFunctor ℓSet {C} {D} {E} c e H K = functor PCF₀ PCF₁ PCF-id PCF-compose
  where
    PCF₀ : Obj ((D op) ×C D) → Obj SetCat
    PCF₀ (d' , d) = [ H ]₀ (d' , c) × [ K ]₀ (e , d)
    
    PCF₁ : {a b : Obj ((D op) ×C D)} → Hom ((D op) ×C D) a b → Hom SetCat (PCF₀ a) (PCF₀ b)
    PCF₁ (f' , f) (Hac , Kea) = ([ H ]₁ (f' , id C {c}) Hac) , [ K ]₁ (id E {e} , f) Kea
    
    abstract
      PCF-id : {x : Obj ((D op) ×C D)} → PCF₁ {x} {x} (id ((D op) ×C D)) ≡ id SetCat
      PCF-id {x' , x} = {!!} 
    
    abstract
      PCF-compose : {x y z : Obj ((D op) ×C D)} {f : Hom ((D op) ×C D) x y} {g : Hom ((D op) ×C D) y z} 
                  → PCF₁ ((((D op) ×C D) ∘ g) f) ≡ (SetCat ∘ PCF₁ g) (PCF₁ f)
      PCF-compose = {!!}

composeProfunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} (ℓSet : Level)
                  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
                  → (H : Profunctor ℓSet C D) → (K : Profunctor ℓSet D E)
                  → ( (c : Obj C) (e : Obj E) → CoEnd (composeProfunctorCoendFunctor ℓSet c e H K) )
                  → Profunctor ℓSet C E
composeProfunctor {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓE₀} {ℓE₁} ℓSet {C} {D} {E} H K ∃-CoEnd = functor CF₀ CF₁ {!!} {!!}
  where
    open CoEnd

    PCF : (c : Obj C) (e : Obj E) → Functor (D op ×C D) (SetCat {ℓSet})
    PCF c e = composeProfunctorCoendFunctor ℓSet c e H K

    CoEnd-morph : (c c' : Obj C) (e e' : Obj (E op)) → Hom C c c' → Hom (E op) e e' → Hom SetCat (co-∫ (∃-CoEnd c e)) (co-∫ (∃-CoEnd c' e'))
    CoEnd-morph c c' e e' fc fe ∫-ce = CoWedge.co-e (CoEnd.co-e (∃-CoEnd c' e')) {!!} ({!!} , {!!})
    
    CF₀ : Obj ((E op) ×C C) → Obj (SetCat {ℓSet})
    CF₀ (e , c) = co-∫ (∃-CoEnd c e)
    
    CF₁ : {a b : Obj ((E op) ×C C)} → Hom ((E op) ×C C) a b → Hom SetCat (CF₀ a) (CF₀ b)
    CF₁ {a' , a} {b' , b} (f' , f) CFa = {!!}
  {-
record CoWedge {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) (w : Obj X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₁) where
  constructor cowedge
  private
    _∘X_ = _∘_ X
  field
    co-e : (c : Obj C) → Hom X (F₀ F (c , c)) w

    co-coher : {c c' : Obj C} (f : Hom C c c') 
          → co-e c' ∘X F₁ F (id C {c'} , f) ≡ co-e c ∘X F₁ F (f , id C {c}) 
-}

{-
record CoEnd {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₀ ⊔ ℓX₁) where
  constructor coend
  field
    co-∫ : Obj X
    co-e : CoWedge F co-∫
    
    
    co-universal : {co-∫' : Obj X} (co-e' : CoWedge F co-∫') → ∃ λ (f : Hom X co-∫ co-∫') → (IsUnique f) × (CoWedge.co-e co-e' ≡ CoWedge.co-e (CoWedge.co-compose co-e f))
-}
