
module Theory.Subcategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Theory.Category


open Category renaming ( _∘_ to comp )

record Subcategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor subcategory
  _∘_ = comp C
  
  field
    SubObj : SubsetOf (Obj C)
    SubHom : (a : Obj C) → (b : Obj C) → SubsetOf (Hom C a b)
    
    closedMorphs : {a b : Obj C} → (f : Hom C a b) 
                 → f ∈ SubHom a b → (a ∈ SubObj) × (b ∈ SubObj)
    
    closedComp : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c)
                → (f ∈ SubHom a b) → (g ∈ SubHom b c) → ((g ∘ f) ∈ SubHom a c)
    
    closedId : {a : Obj C} → (a ∈ SubObj) → (id C ∈ SubHom a a)

open Subcategory

Subcategory→Category : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} 
                     → Subcategory C → Category {ℓ₀} {ℓ₁}
Subcategory→Category {ℓ₀} {ℓ₁} {C} S =  record
  { Obj = ObjS
  ; Hom = HomS
  ; _∘_ = λ {a} {b} {c} → _∘S_ {a} {b} {c}
  ; id = λ {a} → idS {a}
  ; assoc = λ {a} {b} {c} {d} → assocS {a} {b} {c} {d}
  ; idL = {!!}
  ; idR = {!!}
  } where
    _∘C_ = _∘_ S
    
    ObjS : Set ℓ₀
    ObjS = ∃ λ (a : Obj C) → (a ∈ SubObj S)

    HomS : ObjS → ObjS → Set ℓ₁
    HomS (a , a∈S) (b , b∈S) = ∃ λ (f : Hom C a b) → (f ∈ SubHom S a b)
    
    _∘S_ : {a b c : ObjS} → HomS b c → HomS a b → HomS a c
    _∘S_ (f , f∈S) (g , g∈S) = f ∘C g , closedComp S g f g∈S f∈S
    
    idS : {a : ObjS} → HomS a a
    idS {a , a∈S} = id C {a} , closedId S a∈S
    
    assocS : {a b c d : ObjS} {f : HomS a b} {g : HomS b c} {h : HomS c d}
           → h ∘S (g ∘S f) ≡ (h ∘S g) ∘S f
    assocS {a , a∈S} {b , b∈S} {c , c∈S} {d , d∈S} {f , f∈S} {g , g∈S} {h , h∈S} = {!!}
