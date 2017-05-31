
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Constant
open import Theory.Functor.Application
open import Theory.Natural.ExtranaturalTransformation

module Theory.End.Wedge where

open Category
open Functor renaming (id to fun-id ; compose to fun-compose)

--------------------------------------------------------------------------------
-- Definition of wedges
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record Wedge {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (w : Obj X) (F : Functor (C op ×C C) X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₁) where
  constructor wedge
  private
    _∘X_ = _∘_ X
  field
    e : (c : Obj C) → Hom X w (F₀ F (c , c))

    coher : {c c' : Obj C} (f : Hom C c c') 
          → F₁ F (f , id C {c'}) ∘X e c' ≡ F₁ F (id C {c} , f) ∘X e c 

  compose : {v : Obj X} → (f : Hom X v w) → Wedge v F
  compose {v} f = record 
    { e = λ c → e c ∘X f 
    ; coher = λ g → trans (assoc X) (trans (cong (λ Y → Y ∘X f) (coher g)) (sym (assoc X))) 
    }

  open Theory.Functor.Application.TriFunctor
  
  extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
               → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁})
               → ExtranaturalTransformation (constFunctor (A ×C B op ×C B) X w) (Tri[ F ]₂₃)
  extranatural A B = record
    { η = λ a b c → e c 
    ; η-natural = λ b c {a} {a'} {f} → trans (cong (λ Y → Y ∘X e c) (fun-id F)) (trans (right-id X) (trans (sym (left-id X)) (sym (cong (λ Y → e c ∘X Y) refl)))) 
    ; extranatural = λ a b f → coher f 
    ; extranatural-op = λ a c f → refl
    }

wedge-eq : {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} 
         → {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} 
         → {w : Obj X}
         → {F : Functor (C op ×C C) X} 
         → {e₀ : (c : Obj C) → Hom X w (F₀ F (c , c))}
         → {e₁ : (c : Obj C) → Hom X w (F₀ F (c , c))}
         → {coher₀ : {c c' : Obj C} (f : Hom C c c') → _∘_ X (F₁ F (f , id C {c'})) (e₀ c') ≡ _∘_ X (F₁ F (id C {c} , f)) (e₀ c)}
         → {coher₁ : {c c' : Obj C} (f : Hom C c c') → _∘_ X (F₁ F (f , id C {c'})) (e₁ c') ≡ _∘_ X (F₁ F (id C {c} , f)) (e₁ c)}
         → e₀ ≡ e₁
         → wedge {C = C} {X} {w} {F} e₀ coher₀ ≡ wedge {C = C} {X} {w} {F} e₁ coher₁
wedge-eq {C = C} {X} {w} {F} {e} {.e} {coher₀} {coher₁} refl 
  = cong (wedge {C = C} {X} {w} {F} e) 
  $ implicit-fun-ext $ λ c → implicit-fun-ext $ λ c' → fun-ext 
  $ λ f → proof-irrelevance (coher₀ f) (coher₁ f)

--------------------------------------------------------------------------------
-- Definition of cowedges
-- See: https://ncatlab.org/nlab/show/end#explicit_definition
--------------------------------------------------------------------------------

record CoWedge {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} (F : Functor (C op ×C C) X) (w : Obj X) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓX₁) where
  constructor cowedge
  private
    _∘X_ = _∘_ X
  field
    co-e : (c : Obj C) → Hom X (F₀ F (c , c)) w

    co-coher : {c c' : Obj C} (f : Hom C c c') 
          → co-e c' ∘X F₁ F (id C {c'} , f) ≡ co-e c ∘X F₁ F (f , id C {c}) 

  co-compose : {v : Obj X} → (f : Hom X w v) → CoWedge F v
  co-compose {v} f = record 
    { co-e = λ c → f ∘X co-e c  
    ; co-coher = λ g → trans (sym (assoc X)) (trans (cong (λ Y → f ∘X Y) (co-coher g)) (assoc X)) 
    } 

  open Theory.Functor.Application.TriFunctor
  
  extranatural : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} 
               → (A : Category {ℓA₀} {ℓA₁}) (B : Category {ℓB₀} {ℓB₁})
               → ExtranaturalTransformation (Tri[ F ]₂₃) (constFunctor (A ×C B op ×C B) X w)
  extranatural A B = record
    { η = λ a b c → co-e b 
    ; η-natural = λ b c {a} {a'} {f} → trans (right-id X) (trans (sym (left-id X)) (cong (λ Y → co-e b ∘X Y) (sym (fun-id F))))
    ; extranatural = λ a b f → refl 
    ; extranatural-op = λ a c f → co-coher f
    }

cowedge-eq : {ℓC₀ ℓC₁ ℓX₀ ℓX₁ : Level} 
           → {C : Category {ℓC₀} {ℓC₁}} {X : Category {ℓX₀} {ℓX₁}} 
           → {F : Functor (C op ×C C) X} 
           → {w : Obj X}
           → {co-e₀ : (c : Obj C) → Hom X (F₀ F (c , c)) w}
           → {co-e₁ : (c : Obj C) → Hom X (F₀ F (c , c)) w}
           → {coher₀ : {c c' : Obj C} (f : Hom C c c') → _∘_ X (co-e₀ c') (F₁ F (id C {c'} , f)) ≡ _∘_ X (co-e₀ c) (F₁ F (f , id C {c}))}
           → {coher₁ : {c c' : Obj C} (f : Hom C c c') → _∘_ X (co-e₁ c') (F₁ F (id C {c'} , f)) ≡ _∘_ X (co-e₁ c) (F₁ F (f , id C {c}))}
           → co-e₀ ≡ co-e₁
           → cowedge {C = C} {X} {F} {w} co-e₀ coher₀ ≡ cowedge {C = C} {X} {F} {w} co-e₁ coher₁
cowedge-eq {C = C} {X} {F} {w} {co-e} {.co-e} {coher₀} {coher₁} refl 
  = cong (cowedge {C = C} {X} {F} {w} co-e) 
  $ implicit-fun-ext $ λ c → implicit-fun-ext $ λ c' → fun-ext 
  $ λ f → proof-irrelevance (coher₀ f) (coher₁ f)
