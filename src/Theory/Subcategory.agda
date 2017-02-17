
module Theory.Subcategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities hiding ( _∈_ )
open import ProofIrrelevance
open import Theory.Category


open Category renaming ( _∘_ to comp )

record Subcategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor subcategory
  _∘_ = comp C
  
  field
    SubObj : PropSubsetOf (Obj C)
    SubHom : (a : Obj C) → (b : Obj C) → PropSubsetOf (Hom C a b)
    
    closedMorphs : {a b : Obj C} → (f : Hom C a b)
                 → (proj₁ $ SubHom a b f) → (proj₁ $ SubObj a) × (proj₁ $ SubObj b)
    
    closedComp : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c) 
               → (proj₁ $ SubHom a b f) → (proj₁ $ SubHom b c g) → (proj₁ $ SubHom a c (g ∘ f))
    
    closedId : {a : Obj C} → (proj₁ $ SubObj a) → (proj₁ $ SubHom a a (id C))

open Subcategory

Subcategory→Category : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} 
                     → Subcategory C → Category {ℓ₀} {ℓ₁}
Subcategory→Category {ℓ₀} {ℓ₁} {C} S =  record
  { Obj = ObjS
  ; Hom = HomS
  ; _∘_ = λ {a} {b} {c} → _∘S_ {a} {b} {c}
  ; id = λ {a} → idS {a}
  ; assoc = λ {a} {b} {c} {d} → assocS {a} {b} {c} {d}
  ; idL = λ {a} {b} → idLS {a} {b}
  ; idR = λ {a} {b} → idRS {a} {b}
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
    
    helper : {a b : Obj C} → (f g : Hom C a b)
           → (f∈S : f ∈ SubHom S a b) → (g∈S : g ∈ SubHom S a b)
           → f ≡ g → (f , f∈S) ≡ (g , g∈S)
    helper {a} {b} f .f f∈S g∈S refl = cong (λ X → (f , X)) (proof-irr-PropSubset (SubHom S a b) f f∈S g∈S)
    
    assocS : {a b c d : ObjS} {f : HomS a b} {g : HomS b c} {h : HomS c d}
           → _∘S_ {a} {c} {d} h (_∘S_ {a} {b} {c} g f) ≡ _∘S_ {a} {b} {d} (_∘S_ {b} {c} {d} h g) f
    assocS {a , a∈S} {b , b∈S} {c , c∈S} {d , d∈S} {f , f∈S} {g , g∈S} {h , h∈S} 
      = helper (h ∘C (g ∘C f)) ((h ∘C g) ∘C f) 
               (closedComp S (g ∘C f) h (closedComp S f g f∈S g∈S) h∈S) 
               (closedComp S f (h ∘C g) f∈S (closedComp S g h g∈S h∈S))
               (assoc C {f = f} {g} {h})
    
    idLS : {a b : ObjS} {f : HomS a b} → _∘S_ {a} {a} {b} f (idS {a}) ≡ f
    idLS {a , a∈S} {b , b∈S} {f , f∈S} 
      = helper (f ∘C id C {a}) f 
               (closedComp S (id C {a}) f (closedId S a∈S) f∈S) 
               f∈S (idL C)
    
    idRS : {a b : ObjS} {f : HomS a b} → _∘S_ {a} {b} {b} (idS {b}) f ≡ f
    idRS {a , a∈S} {b , b∈S} {f , f∈S} 
      = helper (id C {b} ∘C f) f 
               (closedComp S f (id C {b}) f∈S (closedId S b∈S)) 
               f∈S (idR C)

fullSubcategory : {ℓ₀ ℓ₁ : Level} → (C : Category {ℓ₀} {ℓ₁}) → Subcategory C
fullSubcategory C = record 
  { SubObj = λ a → Lift ⊤ , ⊤-pi
  ; SubHom = λ a b f → Lift ⊤ , ⊤-pi
  ; closedMorphs = λ f f∈S → lift tt , lift tt
  ; closedComp = λ f g f∈S g∈S → lift tt
  ; closedId = λ a∈S → lift tt
  } where
    ⊤-pi : {ℓ : Level} → (x y : Lift {ℓ = ℓ} ⊤) → x ≡ y
    ⊤-pi (lift tt) (lift tt) = refl
    
    
