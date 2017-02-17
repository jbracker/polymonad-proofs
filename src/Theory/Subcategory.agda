
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- Local
open import ProofIrrelevance
open import Congruence
open import Extensionality
open import Theory.Category hiding ( category )

module Theory.Subcategory where

open Category renaming ( _∘_ to comp )

-------------------------------------------------------------------------------
-- Definition of a Subcategory
-------------------------------------------------------------------------------
record Subcategory {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor subcategory
  
  private
    _∘_ = comp C
  
  category = C
  
  field
    SubObj : PropSubsetOf (Obj C)
    SubHom : (a : Obj C) → (b : Obj C) → PropSubsetOf (Hom C a b)
    
    closed-morphisms : {a b : Obj C} → (f : Hom C a b)
                     → f ∈ SubHom a b → a ∈ SubObj × b ∈ SubObj
    
    closed-composition : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c) 
                       → f ∈ SubHom a b → g ∈ SubHom b c → (g ∘ f) ∈ SubHom a c 
    
    closed-id : {a : Obj C} → a ∈ SubObj → id C ∈ SubHom a a

open Subcategory

-------------------------------------------------------------------------------
-- Equality of Subcategories
-------------------------------------------------------------------------------

subcategory-eq : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}}
               → {SubObjA : PropSubsetOf (Obj C)}
               → {SubObjB : PropSubsetOf (Obj C)}
               → {SubHomA : (a : Obj C) → (b : Obj C) → PropSubsetOf (Hom C a b)}
               → {SubHomB : (a : Obj C) → (b : Obj C) → PropSubsetOf (Hom C a b)}
               → {closed-morphisms-A : {a b : Obj C} → (f : Hom C a b) → f ∈ SubHomA a b → a ∈ SubObjA × b ∈ SubObjA}
               → {closed-morphisms-B : {a b : Obj C} → (f : Hom C a b) → f ∈ SubHomB a b → a ∈ SubObjB × b ∈ SubObjB}
               → {closed-composition-A : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c) → f ∈ SubHomA a b → g ∈ SubHomA b c → (comp C g f) ∈ SubHomA a c}
               → {closed-composition-B : {a b c : Obj C} → (f : Hom C a b) → (g : Hom C b c) → f ∈ SubHomB a b → g ∈ SubHomB b c → (comp C g f) ∈ SubHomB a c}
               → {closed-id-A : {a : Obj C} → a ∈ SubObjA → id C ∈ SubHomA a a}
               → {closed-id-B : {a : Obj C} → a ∈ SubObjB → id C ∈ SubHomB a a}
               → SubObjA ≡ SubObjB
               → SubHomA ≡ SubHomB
               → subcategory {C = C} SubObjA SubHomA closed-morphisms-A closed-composition-A closed-id-A
               ≡ subcategory {C = C} SubObjB SubHomB closed-morphisms-B closed-composition-B closed-id-B
subcategory-eq {C = C} {SubObjA} {.SubObjA} {SubHomA} {.SubHomA} {closed-morph-A} {closed-morph-B} {closed-comp-A} {closed-comp-B} {closed-id-A} {closed-id-B} refl refl
  = cong₃ (subcategory SubObjA SubHomA) 
          (implicit-fun-ext (λ a → implicit-fun-ext (λ b → fun-ext (λ f → fun-ext (λ f∈S → 
            proof-irr-× (proof-irr-PropSubset SubObjA a) (proof-irr-PropSubset SubObjA b) (closed-morph-A f f∈S) (closed-morph-B f f∈S)))))) 
          (implicit-fun-ext (λ a → implicit-fun-ext (λ b → implicit-fun-ext (λ c → 
            fun-ext (λ f → fun-ext (λ g → fun-ext (λ f∈S → fun-ext (λ g∈S → 
              proof-irr-PropSubset (SubHomA a c) (comp C g f) (closed-comp-A f g f∈S g∈S) (closed-comp-B f g f∈S g∈S))))))))) 
          (implicit-fun-ext (λ a → fun-ext (λ a∈S → 
            proof-irr-PropSubset (SubHomA a a) (id C) (closed-id-A a∈S) (closed-id-B a∈S))))

-------------------------------------------------------------------------------
-- Properties of Subcategories
-------------------------------------------------------------------------------

Subcategory→Category : {ℓ₀ ℓ₁ : Level} {C : Category {ℓ₀} {ℓ₁}} 
                     → Subcategory C → Category {ℓ₀} {ℓ₁}
Subcategory→Category {ℓ₀} {ℓ₁} {C} S =  record
  { Obj = ObjS
  ; Hom = HomS
  ; _∘_ = λ {a} {b} {c} → _∘S_ {a} {b} {c}
  ; id = λ {a} → idS {a}
  ; assoc = λ {a} {b} {c} {d} → assocS {a} {b} {c} {d}
  ; left-id = λ {a} {b} → left-id-S {a} {b}
  ; right-id = λ {a} {b} → right-id-S {a} {b}
  } where
    _∘C_ = Category._∘_ (category S)
    
    ObjS : Set ℓ₀
    ObjS = ∃ λ (a : Obj C) → (a ∈ SubObj S)

    HomS : ObjS → ObjS → Set ℓ₁
    HomS (a , a∈S) (b , b∈S) = ∃ λ (f : Hom C a b) → (f ∈ SubHom S a b)
    
    _∘S_ : {a b c : ObjS} → HomS b c → HomS a b → HomS a c
    _∘S_ (f , f∈S) (g , g∈S) = f ∘C g , closed-composition S g f g∈S f∈S
    
    idS : {a : ObjS} → HomS a a
    idS {a , a∈S} = id C {a} , closed-id S a∈S
    
    helper : {a b : Obj C} → (f g : Hom C a b)
           → (f∈S : f ∈ SubHom S a b) → (g∈S : g ∈ SubHom S a b)
           → f ≡ g → (f , f∈S) ≡ (g , g∈S)
    helper {a} {b} f .f f∈S g∈S refl = cong (λ X → (f , X)) (proof-irr-PropSubset (SubHom S a b) f f∈S g∈S)
    
    assocS : {a b c d : ObjS} {f : HomS a b} {g : HomS b c} {h : HomS c d}
           → _∘S_ {a} {c} {d} h (_∘S_ {a} {b} {c} g f) ≡ _∘S_ {a} {b} {d} (_∘S_ {b} {c} {d} h g) f
    assocS {a , a∈S} {b , b∈S} {c , c∈S} {d , d∈S} {f , f∈S} {g , g∈S} {h , h∈S} 
      = helper (h ∘C (g ∘C f)) ((h ∘C g) ∘C f) 
               (closed-composition S (g ∘C f) h (closed-composition S f g f∈S g∈S) h∈S) 
               (closed-composition S f (h ∘C g) f∈S (closed-composition S g h g∈S h∈S))
               (assoc C {f = f} {g} {h})
    
    left-id-S : {a b : ObjS} {f : HomS a b} → _∘S_ {a} {a} {b} f (idS {a}) ≡ f
    left-id-S {a , a∈S} {b , b∈S} {f , f∈S} 
      = helper (f ∘C id C {a}) f 
               (closed-composition S (id C {a}) f (closed-id S a∈S) f∈S) 
               f∈S (left-id C)
    
    right-id-S : {a b : ObjS} {f : HomS a b} → _∘S_ {a} {b} {b} (idS {b}) f ≡ f
    right-id-S {a , a∈S} {b , b∈S} {f , f∈S} 
      = helper (id C {b} ∘C f) f 
               (closed-composition S f (id C {b}) f∈S (closed-id S b∈S)) 
               f∈S (right-id C)

fullSubcategory : {ℓ₀ ℓ₁ : Level} → (C : Category {ℓ₀} {ℓ₁}) → Subcategory C
fullSubcategory C = record 
  { SubObj = λ a → Lift ⊤ , proof-irr-Lift proof-irr-⊤
  ; SubHom = λ a b f → Lift ⊤ , proof-irr-Lift proof-irr-⊤
  ; closed-morphisms = λ f f∈S → lift tt , lift tt
  ; closed-composition = λ f g f∈S g∈S → lift tt
  ; closed-id = λ a∈S → lift tt
  }
    
