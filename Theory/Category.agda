
module Theory.Category where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Category {ℓ₀ ℓ₁ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    Obj : Set ℓ₀
    Hom : Obj → Obj → Set ℓ₁
    
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id : ∀ {a} → Hom a a
    
    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    idL : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    idR : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f

open Category

productCategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} → Category {ℓC₀} {ℓC₁} → Category {ℓD₀} {ℓD₁} → Category
productCategory {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} C D = record
  { Obj = ObjP
  ; Hom = HomP
  ; _∘_ = _∘P_
  ; id = idP
  ; assoc = cong₂ (λ X Y → X , Y) (assoc C) (assoc D)
  ; idL = cong₂ (λ X Y → X , Y) (idL C) (idL D)
  ; idR = cong₂ (λ X Y → X , Y) (idR C) (idR D)
  } where
    ObjP = Obj C × Obj D

    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    
    HomP : ObjP → ObjP → Set (ℓD₁ ⊔ ℓC₁)
    HomP (ca , da) (cb , db) = Hom C ca cb × Hom D da db
    
    _∘P_ : {a b c : ObjP} → HomP b c → HomP a b → HomP a c
    _∘P_ (cf , df) (cg , dg) = cf ∘C cg , df ∘D dg 
    
    idP : {a : ObjP} → HomP a a
    idP {ca , da} = id C {ca} , id D {da}

_×C_ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} → Category {ℓC₀} {ℓC₁} → Category {ℓD₀} {ℓD₁} → Category
C ×C D = productCategory C D
