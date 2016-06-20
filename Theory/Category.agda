
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

-------------------------------------------------------------------------------
-- Definition of Categories
-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
-- The Unit Category
-------------------------------------------------------------------------------

-- The unit category with exactly one element and one morphism.
unitCategory : Category
unitCategory = record
  { Obj = ⊤
  ; Hom = λ _ _ → ⊤
  ; _∘_ = λ _ _ → tt
  ; id = tt
  ; assoc = refl
  ; idL = refl
  ; idR = refl
  }

⊤-Cat = unitCategory

-------------------------------------------------------------------------------
-- Lifting of Categories to another Level
-------------------------------------------------------------------------------
open Category

liftCategory : {ℓC₀ ℓC₁ ℓL₀ ℓL₁ : Level} → Category {ℓC₀} {ℓC₁} → Category {ℓ₀ = ℓC₀ ⊔ ℓL₀} {ℓ₁ = ℓC₁ ⊔ ℓL₁}
liftCategory {ℓC₀} {ℓC₁} {ℓL₀} {ℓL₁} C = record
  { Obj = ObjL
  ; Hom = HomL
  ; _∘_ = _∘L_
  ; id = idLift
  ; assoc = assocL
  ; idL = trans shiftL (cong lift (idL C))
  ; idR = trans shiftL (cong lift (idR C))
  } where
    ObjL : Set (ℓC₀ ⊔ ℓL₀)
    ObjL = Lift {ℓ = ℓL₀} (Obj C)

    HomL : ObjL → ObjL → Set (ℓC₁ ⊔ ℓL₁) 
    HomL (lift a) (lift b) = Lift {ℓ = ℓL₁} (Hom C a b)
    
    _∘C_ = _∘_ C
    
    _∘L_ : {a b c : ObjL} → HomL b c → HomL a b → HomL a c
    _∘L_ (lift f) (lift g) = lift (f ∘C g)
    
    idLift : {a : ObjL} → HomL a a
    idLift = lift (id C)
    
    shiftL :  {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
           → lift g ∘L lift f ≡ lift (g ∘C f)
    shiftL = refl
    
    assocL : {a b c d : ObjL} {f : HomL a b} {g : HomL b c} {h : HomL c d} 
           → h ∘L (g ∘L f) ≡ (h ∘L g) ∘L f
    assocL {f = lift f} {lift g} {lift h} = begin
      lift h ∘L (lift g ∘L lift f) 
        ≡⟨ cong (λ X → lift h ∘L X) shiftL ⟩ 
      lift h ∘L lift (g ∘C f) 
        ≡⟨ shiftL ⟩ 
      lift (h ∘C (g ∘C f))
        ≡⟨ cong lift (assoc C) ⟩
      lift ((h ∘C g) ∘C f)
        ≡⟨ sym shiftL ⟩
      lift (h ∘C g) ∘L lift f 
        ≡⟨ cong (λ X → X ∘L lift f) (sym shiftL) ⟩
      (lift h ∘L lift g) ∘L lift f ∎

-------------------------------------------------------------------------------
-- Product of Categories
-------------------------------------------------------------------------------
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

_×C_ = productCategory
