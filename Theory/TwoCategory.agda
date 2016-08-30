
module Theory.TwoCategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Examples.Functor

-------------------------------------------------------------------------------
-- Definition of 2-Categories
-------------------------------------------------------------------------------

open Category hiding ( idL ; idR ; assoc ) renaming ( id to idC )

record StrictTwoCategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    -- Names and structure base on: https://ncatlab.org/nlab/show/strict+2-category
    --                              https://ncatlab.org/nlab/show/bicategory
    
    Cell₀ : Set ℓ₀
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

    --                       (b c × a b ↦ a c)
    comp : {a b c : Cell₀} → Functor (HomCat b c ×C HomCat a b) (HomCat a c) 
    id₁  : {a : Cell₀} → Obj (HomCat a a)
    
    horizontalIdL₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
                   → [ comp {a} {a} {b} ]₀ (f , id₁ {a}) ≡ f
    
    horizontalIdL₂ : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                   → [ comp {a} {a} {b} ]₁ (η , idC (HomCat a a)) ≡ subst₂ (Hom (HomCat a b)) (sym horizontalIdL₁) (sym horizontalIdL₁) η
    
    horizontalIdR₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
                   → [ comp {a} {b} {b} ]₀ (id₁ {b} , f) ≡ f
    
    horizontalIdR₂ : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                   → [ comp {a} {b} {b} ]₁ (idC (HomCat b b), η) ≡ subst₂ (Hom (HomCat a b)) (sym horizontalIdR₁) (sym horizontalIdR₁) η

    horizontalAssoc₁ : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h : Obj (HomCat c d)}
                     → [ comp ]₀ (h , [ comp ]₀ (g , f)) ≡ [ comp ]₀ ([ comp ]₀ (h , g) , f)
    
    horizontalAssoc₂ : {a b c d : Cell₀} {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
                     → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
                     → ([ comp ]₁ (η , [ comp ]₁ (θ , ι))) ≡ subst₂ (Hom (HomCat a d)) (sym horizontalAssoc₁) (sym horizontalAssoc₁) ([ comp ]₁ ([ comp ]₁ (η , θ) , ι))
    
    whiskerCoher1' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h i : Obj (HomCat c d)} {η : Hom (HomCat c d) h i}
                   → [ comp ]₁ (η , idC (HomCat a c)) 
                   ≡ subst₂ (Hom (HomCat a d)) (sym (horizontalAssoc₁ {f = f} {g = g})) (sym horizontalAssoc₁) ([ comp ]₁ ([ comp ]₁ (η , idC (HomCat b c)) , idC (HomCat a b)))
    
    whiskerCoher2' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g h : Obj (HomCat b c)} {i : Obj (HomCat c d)} {η : Hom (HomCat b c) g h} 
                   → Functor.F₁ comp {a = i , [ comp ]₀ (g , f)} (idC (HomCat c d) , (Functor.F₁ comp {a = g , f} (η , idC (HomCat a b)))) 
                   ≡ subst₂ (Hom (HomCat a d)) (sym horizontalAssoc₁) (sym horizontalAssoc₁) ([ comp ]₁ ([ comp ]₁ (idC (HomCat c d) , η) , idC (HomCat a b)))
    
    whiskerCoher3' : {a b c d : Cell₀} {f g : Obj (HomCat a b)} {h : Obj (HomCat b c)} {i : Obj (HomCat c d)} {η : Hom (HomCat a b) f g}
                   → Functor.F₁ comp {a = i , [ comp ]₀ (h , f)} (idC (HomCat c d) , Functor.F₁ comp {a = h , f} (idC (HomCat b c) , η)) 
                   ≡ subst₂ (Hom (HomCat a d)) (sym horizontalAssoc₁) (sym horizontalAssoc₁) ([ comp ]₁ (idC (HomCat b d) {- [ comp ]₀ (i , h)) -} , η))
    
    whiskerCoher4' : {a b c : Cell₀} {f g : Obj (HomCat a b)} {h i : Obj (HomCat b c)} {η : Hom (HomCat a b) f g} {θ : Hom (HomCat b c) h i}
                   → Category._∘_ (HomCat a c) ([ comp ]₁ (idC (HomCat b c) , η)) ([ comp ]₁ (θ , idC (HomCat a b))) 
                   ≡ Category._∘_ (HomCat a c) ([ comp ]₁ (θ , idC (HomCat a b))) ([ comp ]₁ (idC (HomCat b c) , η))
  
  
  Cell₁ : Cell₀ → Cell₀ → Set ℓ₁
  Cell₁ a b = Obj (HomCat a b)
  
  Cell₂ : {a b : Cell₀} → (f g : Cell₁ a b) → Set ℓ₂
  Cell₂ {a} {b} f g = Hom (HomCat a b) f g  
  
  id₂ : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f f
  id₂ {a} {b} = Category.id (HomCat a b)

  -- Horizontal composition
  _∘ₕ_ : {a b c : Cell₀} → Cell₁ b c → Cell₁ a b → Cell₁ a c
  _∘ₕ_ f g = [ comp ]₀ (f , g)

  _∘ₕ₂_ : {a b c : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c}
        → Cell₂ g g' → Cell₂ f f' → Cell₂ (g ∘ₕ f) (g' ∘ₕ f')
  _∘ₕ₂_ η θ = [ comp ]₁ (η , θ)

  -- Vertical composition
  _∘ᵥ_ : {a b : Cell₀} {f g h : Cell₁ a b} → Cell₂ g h → Cell₂ f g → Cell₂ f h
  _∘ᵥ_ {a = a} {b = b} η θ = Category._∘_ (HomCat a b) η θ
  
  -- Right whiskering
  _▷_ : {a b c : Cell₀} {f g : Cell₁ a b} 
      → (h : Cell₁ b c) → Cell₂ f g → Cell₂ (h ∘ₕ f) (h ∘ₕ g)
  _▷_ {b = b} {c = c} h η = id₂ {b} {c} ∘ₕ₂ η

  -- Left whiskering
  _◁_ : {a b c : Cell₀} {f g : Cell₁ b c} 
      → Cell₂ f g → (h : Cell₁ a b) → Cell₂ (f ∘ₕ h) (g ∘ₕ h)
  _◁_ {a = a} {b = b} η h = η ∘ₕ₂ id₂ {a} {b}
  
  -- The functor designated by id
  id→functor : {a : Cell₀} → Functor ⊤-Cat (HomCat a a)
  id→functor {a} = constFunctor (HomCat a a) (id₁ {a})

  vIdL : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ ≡ θ
  vIdL {a} {b} = Category.idL (HomCat a b)

  vIdR : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ ∘ᵥ θ ≡ θ
  vIdR {a} {b} = Category.idR (HomCat a b)
  
  vAssoc : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {θ : Cell₂ g h} {ι : Cell₂ h i}
                → ι ∘ᵥ (θ ∘ᵥ η) ≡ (ι ∘ᵥ θ) ∘ᵥ η
  vAssoc {a} {b} = Category.assoc (HomCat a b)
  
  hIdL₁ : {a b : Cell₀} {f : Cell₁ a b} → f ∘ₕ id₁ {a} ≡ f
  hIdL₁ = horizontalIdL₁
  
  hIdR₁ :  {a b : Cell₀} {f : Cell₁ a b} → id₁ {b} ∘ₕ f ≡ f
  hIdR₁ = horizontalIdR₁

  hIdL₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
        → η ∘ₕ₂ id₂ {a} {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  hIdL₂ = horizontalIdL₂

  hIdR₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
        → id₂ {b} {b} ∘ₕ₂ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  hIdR₂ = horizontalIdR₂
  
  hAssoc₁ : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
          → h ∘ₕ (g ∘ₕ f) ≡ (h ∘ₕ g) ∘ₕ f
  hAssoc₁ = horizontalAssoc₁

  hAssoc₂ : {a b c d : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
          → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
          → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ∘ₕ₂ θ) ∘ₕ₂ ι)
  hAssoc₂ = horizontalAssoc₂
  
  whiskerLeftId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} 
                → id₂ {f = g} ◁ f ≡ id₂ {f = g ∘ₕ f}
  whiskerLeftId₁ = Functor.id comp
  
  whiskerRightId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c}
                 → g ▷ id₂ {f = f} ≡ id₂ {f = g ∘ₕ f}
  whiskerRightId₁ = Functor.id comp
  
  whiskerRightId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  whiskerRightId₂ = horizontalIdL₂
  
  whiskerLeftId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  whiskerLeftId₂ = horizontalIdR₂

  whiskerRightDist : {a b c : Cell₀} {f : Cell₁ a b} {g h i : Cell₁ b c} {η : Cell₂ g h} {θ : Cell₂ h i}
                  → (θ ◁ f) ∘ᵥ (η ◁ f) ≡ (θ ∘ᵥ η) ◁ f
  whiskerRightDist {a} {b} {c} {f} {η = η} {θ} = 
    let _∘bc_ = Category._∘_ (HomCat b c)
    in trans (sym (Functor.dist comp)) (cong (λ X → [ comp ]₁ (θ ∘bc η , X)) vIdL)

  whiskerLeftDist : {a b c : Cell₀} {f g h : Cell₁ a b} {i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ g h}
                   → (i ▷ θ) ∘ᵥ (i ▷ η) ≡ i ▷ (θ ∘ᵥ η)
  whiskerLeftDist {a} {b} {c} {η = η} {θ} = 
    let _∘ab_ = Category._∘_ (HomCat a b)
    in trans (sym (Functor.dist comp)) (cong (λ X → [ comp ]₁ (X , θ ∘ab η)) vIdL)
  
  
  whiskerCoher1 : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                 → η ◁ (g ∘ₕ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ◁ g) ◁ f)
  whiskerCoher1 = whiskerCoher1'

  whiskerCoher2 : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                → i ▷ (η ◁ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ▷ η) ◁ f)
  whiskerCoher2 = whiskerCoher2'
  
  whiskerCoher3 : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                → i ▷ (h ▷ η) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ∘ₕ h) ▷ η)
  whiskerCoher3 = whiskerCoher3'

  whiskerCoher4 : {a b c : Cell₀} {f g : Cell₁ a b} {h i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ h i}
                → (i ▷ η) ∘ᵥ (θ ◁ f) ≡ (θ ◁ g) ∘ᵥ (h ▷ η)
  whiskerCoher4 = whiskerCoher4'

  -- Unitors
  lUnitor : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ (f ∘ₕ id₁) f
  lUnitor {a} {b} {f} = subst₂ Cell₂ (sym $ hIdL₁ {a} {b} {f}) refl (id₂ {a} {b})

  lUnitorInv : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f (f ∘ₕ id₁)
  lUnitorInv {a} {b} {f} = subst₂ Cell₂ refl (sym hIdL₁) (id₂ {a} {b})
  
  λ' : {a b : Cell₀} → (f : Cell₁ a b) → Cell₂ (f ∘ₕ id₁) f
  λ' {a} {b} f = lUnitor {a} {b} {f}
  
  λ'' : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ f (f ∘ₕ id₁)
  λ'' {a} {b} f = lUnitorInv {a} {b} {f}
  
  rUnitor : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ (id₁ ∘ₕ f) f
  rUnitor {a} {b} {f} = subst₂ Cell₂ (sym $ hIdR₁ {a} {b} {f}) refl (id₂ {a} {b})
  
  rUnitorInv : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f (id₁ ∘ₕ f)
  rUnitorInv {a} {b} {f} = subst₂ Cell₂ refl (sym $ hIdR₁ {a} {b} {f}) (id₂ {a} {b})

  ρ : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ (id₁ ∘ₕ f) f
  ρ {a} {b} f = rUnitor {a} {b} {f}
  
  ρ' : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ f (id₁ ∘ₕ f)
  ρ' {a} {b} f = rUnitorInv {a} {b} {f}
  
  private
    substComp₁ : {a b : Cell₀} {f g : Cell₁ a b}
               → (eq : g ≡ f)
               → (subst₂ Cell₂ refl eq id₂) ∘ᵥ (subst₂ Cell₂ eq refl id₂) ≡ id₂ ∘ᵥ id₂
    substComp₁ refl = refl
  
    substComp₂ : {a b : Cell₀} {f g : Cell₁ a b}
               → (eq : g ≡ f)
               → (subst₂ Cell₂ eq refl id₂) ∘ᵥ (subst₂ Cell₂ refl eq id₂) ≡ id₂ ∘ᵥ id₂
    substComp₂ refl = refl
  
  lUnitorId : {a b : Cell₀} {f : Cell₁ a b} 
            → lUnitor {a} {b} {f} ∘ᵥ lUnitorInv {a} {b} {f} ≡ id₂ {f = f}
  lUnitorId {a} {b} {f} = trans (substComp₂ (sym hIdL₁)) vIdL
  
  lUnitorId' : {a b : Cell₀} {f : Cell₁ a b} 
             → lUnitorInv {a} {b} {f} ∘ᵥ lUnitor {a} {b} {f} ≡ id₂
  lUnitorId' {a} {b} {f} = trans (substComp₁ (sym hIdL₁)) vIdL
  
  rUnitorId : {a b : Cell₀} {f : Cell₁ a b} 
            → rUnitor {a} {b} {f} ∘ᵥ rUnitorInv {a} {b} {f} ≡ id₂ {f = f}
  rUnitorId {a} {b} {f} = trans (substComp₂ (sym hIdR₁)) vIdR

  rUnitorId' : {a b : Cell₀} {f : Cell₁ a b} 
             → rUnitorInv {a} {b} {f} ∘ᵥ rUnitor {a} {b} {f} ≡ id₂
  rUnitorId' {a} {b} {f} = trans (substComp₁ (sym hIdR₁)) vIdR
  
  -- Associators
  associator : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
             → Cell₂ (h ∘ₕ (g ∘ₕ f)) ((h ∘ₕ g) ∘ₕ f)
  associator {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ refl hAssoc₁ id₂

  associatorInv : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                → Cell₂ ((h ∘ₕ g) ∘ₕ f) (h ∘ₕ (g ∘ₕ f)) 
  associatorInv {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ hAssoc₁ refl id₂

  associatorId : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
               → associator {f = f} {g} {h} ∘ᵥ associatorInv {f = f} {g} {h} ≡ id₂
  associatorId = trans (substComp₁ hAssoc₁) vIdR
  
  associatorId' : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                → associatorInv {f = f} {g} {h} ∘ᵥ associator {f = f} {g} {h} ≡ id₂
  associatorId' = trans (substComp₂ hAssoc₁) vIdR
  
  α : {a b c d : Cell₀} 
    → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
    → Cell₂ (h ∘ₕ (g ∘ₕ f)) ((h ∘ₕ g) ∘ₕ f)
  α f g h = associator {f = f} {g} {h}
  
  α' : {a b c d : Cell₀} 
     → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
     → Cell₂ ((h ∘ₕ g) ∘ₕ f) (h ∘ₕ (g ∘ₕ f)) 
  α' f g h = associatorInv {f = f} {g} {h}

-------------------------------------------------------------------------------
-- Unit strict 2-category
-------------------------------------------------------------------------------

unitStrictTwoCategory : StrictTwoCategory
unitStrictTwoCategory = record
  { Cell₀ = ⊤
  ; HomCat = HomCat
  ; comp = comp
  ; id₁ = id₁
  ; horizontalIdR₁ = refl
  ; horizontalIdR₂ = refl
  ; horizontalIdL₁ = refl
  ; horizontalIdL₂ = refl
  ; horizontalAssoc₁ = refl
  ; horizontalAssoc₂ = refl
  ; whiskerCoher1' = refl
  ; whiskerCoher2' = refl
  ; whiskerCoher3' = refl
  ; whiskerCoher4' = refl
  } where
    HomCat : ⊤ → ⊤ → Category
    HomCat tt tt = ⊤-Cat
    
    F₀ : Obj (HomCat tt tt ×C HomCat tt tt) → Obj (HomCat tt tt)
    F₀ (tt , tt) = tt
    
    F₁ : {a b : Obj (HomCat tt tt ×C HomCat tt tt)} → Hom (HomCat tt tt ×C HomCat tt tt) a b → Hom (HomCat tt tt) tt tt
    F₁ {tt , tt} {tt , tt} (tt , tt) = tt
    
    comp : {a b c : ⊤} → Functor (HomCat b c ×C HomCat a b) (HomCat a c)
    comp {tt} {tt} {tt} = record 
      { F₀ = F₀
      ; F₁ = F₁
      ; id = refl
      ; dist = refl
      }
    
    id₁ : {a : ⊤} → Obj (HomCat a a)
    id₁ {tt} = tt

⊤-TwoCat = unitStrictTwoCategory

-------------------------------------------------------------------------------
-- Creating a Strict 2-Category from a Category.
-------------------------------------------------------------------------------

Category→StrictTwoCategory : ∀ {ℓ₀ ℓ₁} → Category {ℓ₀} {ℓ₁} → StrictTwoCategory {ℓ₀} {ℓ₁} {lzero}
Category→StrictTwoCategory {ℓ₀} {ℓ₁} C = record
  { Cell₀ = Cell₀
  ; HomCat = HomCat
  ; comp = comp
  ; id₁ = id₁
  ; horizontalIdR₁ = Category.idR C
  ; horizontalIdR₂ = refl
  ; horizontalIdL₁ = Category.idL C
  ; horizontalIdL₂ = refl
  ; horizontalAssoc₁ = Category.assoc C
  ; horizontalAssoc₂ = refl
  ; whiskerCoher1' = refl
  ; whiskerCoher2' = refl
  ; whiskerCoher3' = refl
  ; whiskerCoher4' = refl
  } where
    ℓ₂ = lzero
    _∘C_ = _∘_ C
    
    Cell₀ = Obj C
    
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}
    HomCat a b = record
      { Obj = Hom C a b
      ; Hom = λ f g → ⊤
      ; _∘_ = λ tt tt → tt
      ; id = tt
      ; assoc = refl
      ; idL = refl
      ; idR = refl
      }
    
    comp : {a b c : Cell₀} 
         → Functor (HomCat b c ×C HomCat a b) (HomCat a c)
    comp {a} {b} {c} = record 
      { F₀ = F₀
      ; F₁ = λ {x} {y} → F₁ {x} {y}
      ; id = refl
      ; dist = refl
      } where
          F₀ : Obj (HomCat b c ×C HomCat a b) → Obj (HomCat a c)
          F₀ (g , f) = g ∘C f
          
          F₁ : {x y : Obj (HomCat b c ×C HomCat a b)} 
             → Hom (HomCat b c ×C HomCat a b) x y → Hom (HomCat a c) (F₀ x) (F₀ y)
          F₁ f = tt
    
    id₁ : {a : Cell₀} → Obj (HomCat a a)
    id₁ = idC C

StrictTwoCategory→Category : ∀ {ℓ₀ ℓ₁ ℓ₂} → StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} → Category {ℓ₀} {ℓ₁}
StrictTwoCategory→Category TwoCat = record
  { Obj = StrictTwoCategory.Cell₀ TwoCat
  ; Hom = StrictTwoCategory.Cell₁ TwoCat
  ; _∘_ = λ f g → [ StrictTwoCategory.comp TwoCat ]₀ (f , g)
  ; id = StrictTwoCategory.id₁ TwoCat
  ; assoc = StrictTwoCategory.horizontalAssoc₁ TwoCat
  ; idL = StrictTwoCategory.horizontalIdL₁ TwoCat
  ; idR = StrictTwoCategory.horizontalIdR₁ TwoCat
  } 
