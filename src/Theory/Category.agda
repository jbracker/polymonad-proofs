
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product renaming ( _,_ to _,'_ ; _×_ to _×'_ )
open import Data.Unit
open import Relation.Binary.HeterogeneousEquality hiding ( cong ; cong₂ ; subst ; trans ; sym ; proof-irrelevance ) renaming ( refl to hrefl )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Extensionality
open import Congruence
open import Theory.Triple

module Theory.Category where

-------------------------------------------------------------------------------
-- Definition of Categories
-------------------------------------------------------------------------------
record Category {ℓ₀ ℓ₁ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  constructor category
  field
    Obj : Set ℓ₀
    Hom : Obj → Obj → Set ℓ₁
    
    _∘_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id : ∀ {a} → Hom a a
    
    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    right-id : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    left-id  : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f

-------------------------------------------------------------------------------
-- Propositional equality of categories
-------------------------------------------------------------------------------

category-hom-eq : ∀ {ℓ₀ ℓ₁} 
               → {ObjC ObjD : Set ℓ₀} → (eq₀ : ObjC ≡ ObjD)
               → {HomC : ObjC → ObjC → Set ℓ₁} → {HomD : ObjD → ObjD → Set ℓ₁} → (eq₁ : subst (λ X → (X → X → Set ℓ₁)) eq₀ HomC ≡ HomD)
               → {a b : ObjC} → HomD (subst idF eq₀ a) (subst idF eq₀ b) ≡ HomC a b
category-hom-eq refl refl = refl

category-eq : ∀ {ℓ₀ ℓ₁} 
            → {ObjC : Set ℓ₀}
            → {ObjD : Set ℓ₀}
            → {HomC : ObjC → ObjC → Set ℓ₁}
            → {HomD : ObjD → ObjD → Set ℓ₁}
            → {_∘C_ : ∀ {a b c} → HomC b c → HomC a b → HomC a c}
            → {_∘D_ : ∀ {a b c} → HomD b c → HomD a b → HomD a c}
            → {idC : {a : ObjC} → HomC a a}
            → {idD : {a : ObjD} → HomD a a}
            → {assocC : {a b c d : ObjC} {f : HomC a b} {g : HomC b c} {h : HomC c d} → h ∘C (g ∘C f) ≡ (h ∘C g) ∘C f}
            → {assocD : {a b c d : ObjD} {f : HomD a b} {g : HomD b c} {h : HomD c d} → h ∘D (g ∘D f) ≡ (h ∘D g) ∘D f}
            → {right-idC : {a b : ObjC} {f : HomC a b} → idC ∘C f ≡ f}
            → {right-idD : {a b : ObjD} {f : HomD a b} → idD ∘D f ≡ f}
            → {left-idC : {a b : ObjC} {f : HomC a b} → f ∘C idC ≡ f}
            → {left-idD : {a b : ObjD} {f : HomD a b} → f ∘D idD ≡ f}
            → ObjC ≡ ObjD
            → HomC ≅ HomD
            → (λ {a} {b} {c} → _∘C_ {a} {b} {c}) ≅ (λ {a} {b} {c} → _∘D_ {a} {b} {c})
            → (λ {a} → idC {a}) ≅ (λ {a} → idD {a})
            → category ObjC HomC _∘C_ idC assocC right-idC left-idC ≡ category ObjD HomD _∘D_ idD assocD right-idD left-idD
category-eq {ℓ₀} {ℓ₁} {ObjC} {.ObjC} {HomC} {.HomC}  {_∘C_} {._∘C_} {idC} {.idC} {assocC} {assocD} {right-idC} {right-idD} {left-idC} {left-idD} refl hrefl hrefl hrefl 
  = cong₃ (category ObjC HomC _∘C_ idC) p1 p2 p3
  where
    p1 : (λ {a} {b} {c} {d} {f} {g} {h} → assocC {a} {b} {c} {d} {f} {g} {h}) ≡ assocD
    p1 = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → implicit-fun-ext $ λ c → 
         implicit-fun-ext $ λ d → implicit-fun-ext $ λ f → implicit-fun-ext $ λ g → 
         implicit-fun-ext $ λ h → 
         proof-irrelevance (assocC {a} {b} {c} {d} {f} {g} {h}) (assocD {a} {b} {c} {d} {f} {g} {h})
    p2 : (λ {a} {b} {f} → right-idC {a} {b} {f}) ≡ (λ {a} {b} {f} → right-idD {a} {b} {f})
    p2 = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → implicit-fun-ext $ λ f →
         proof-irrelevance (right-idC {a} {b} {f}) (right-idD {a} {b} {f})
    p3 : (λ {a} {b} {f} → left-idC {a} {b} {f}) ≡ (λ {a} {b} {f} → left-idD {a} {b} {f})
    p3 = implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → implicit-fun-ext $ λ f →
         proof-irrelevance (left-idC {a} {b} {f}) (left-idD {a} {b} {f})

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
  ; left-id = refl
  ; right-id = refl
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
  ; id = left-idift
  ; assoc = assocL
  ; right-id = trans shiftL (cong lift (right-id C))
  ; left-id = trans shiftL (cong lift (left-id C))
  } where
    ObjL : Set (ℓC₀ ⊔ ℓL₀)
    ObjL = Lift {ℓ = ℓL₀} (Obj C)

    HomL : ObjL → ObjL → Set (ℓC₁ ⊔ ℓL₁) 
    HomL (lift a) (lift b) = Lift {ℓ = ℓL₁} (Hom C a b)
    
    _∘C_ = _∘_ C
    
    _∘L_ : {a b c : ObjL} → HomL b c → HomL a b → HomL a c
    _∘L_ (lift f) (lift g) = lift (f ∘C g)
    
    left-idift : {a : ObjL} → HomL a a
    left-idift = lift (id C)
    
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
  ; assoc = cong₂ _,'_ (assoc C) (assoc D)
  ; left-id = cong₂ _,'_ (left-id C) (left-id D)
  ; right-id = cong₂ _,'_ (right-id C) (right-id D)
  } where
    ObjP = Obj C ×' Obj D

    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    
    HomP : ObjP → ObjP → Set (ℓD₁ ⊔ ℓC₁)
    HomP (ca ,' da) (cb ,' db) = Hom C ca cb ×' Hom D da db
    
    _∘P_ : {a b c : ObjP} → HomP b c → HomP a b → HomP a c
    _∘P_ (cf ,' df) (cg ,' dg) = cf ∘C cg ,' df ∘D dg 
    
    idP : {a : ObjP} → HomP a a
    idP {ca ,' da} = id C {ca} ,' id D {da}

_×C_ = productCategory


-------------------------------------------------------------------------------
-- Dual of a category
-------------------------------------------------------------------------------

dualCategory : {ℓC₀ ℓC₁ : Level} → Category {ℓC₀} {ℓC₁} → Category {ℓC₀} {ℓC₁}
dualCategory {ℓC₀} {ℓC₁} C = record
  { Obj = Obj C
  ; Hom = λ a b → Hom C b a
  ; _∘_ = λ {a} {b} {c} f g → _∘_ C g f
  ; id = id C
  ; assoc = sym $ assoc C
  ; right-id = left-id C
  ; left-id = right-id C
  }

_op = dualCategory

-------------------------------------------------------------------------------
-- Triple of Categories
-------------------------------------------------------------------------------
tripleCategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} → Category {ℓC₀} {ℓC₁} → Category {ℓD₀} {ℓD₁} → Category {ℓE₀} {ℓE₁} → Category
tripleCategory {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓE₀} {ℓE₁} C D E = record
  { Obj = ObjP
  ; Hom = HomP
  ; _∘_ = _∘P_
  ; id = idP
  ; assoc = cong₃ _,_,_ (assoc C) (assoc D) (assoc E)
  ; left-id = cong₃ _,_,_ (left-id C) (left-id D) (left-id E)
  ; right-id = cong₃ _,_,_ (right-id C) (right-id D) (right-id E)
  } where
    ObjP = Obj C × Obj D × Obj E

    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    _∘E_ = _∘_ E
    
    HomP : ObjP → ObjP → Set (ℓC₁ ⊔ ℓD₁ ⊔ ℓE₁)
    HomP (ca , da , ea) (cb , db , eb) = Hom C ca cb × Hom D da db × Hom E ea eb
    
    _∘P_ : {a b c : ObjP} → HomP b c → HomP a b → HomP a c
    _∘P_ (cf , df , ef) (cg , dg , eg) = (cf ∘C cg) , (df ∘D dg) , (ef ∘E eg)
    
    idP : {a : ObjP} → HomP a a
    idP {ca , da , ea} = id C {ca} , id D {da} , id E {ea}

_×C_×C_ = tripleCategory
