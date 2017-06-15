
module Theory.TwoCategory.Definition where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; subst to hsubst ; subst₂ to hsubst₂ ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

-- Local
open import Utilities
open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Functor.Examples
open import Theory.Functor.Composition
open import Theory.Functor.Application
open Theory.Functor.Application.BiFunctor
open import Theory.Functor.Association
open Theory.Functor.Association.Triple
open Theory.Functor.Association.BiFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

-------------------------------------------------------------------------------
-- Definition of 2-Categories
-------------------------------------------------------------------------------

open Category hiding ( left-id ; right-id ; assoc ) renaming ( id to idC )

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
  id→functor {a} = constObjFunctor (HomCat a a) (id₁ {a})

  vIdL : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ ≡ θ
  vIdL {a} {b} = Category.left-id (HomCat a b)

  vIdR : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ ∘ᵥ θ ≡ θ
  vIdR {a} {b} = Category.right-id (HomCat a b)
  
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
  
  private
    het-help : {a b : Cell₀} 
             → {f g h k : Cell₁ a b} 
             → (η : Cell₂ f g) (ι : Cell₂ h k)
             → (p : h ≡ f) (q : k ≡ g)
             → η ≡ subst₂ Cell₂ p q ι → η ≅ ι
    het-help η ι refl refl refl = refl
  
  hIdL₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → _∘ₕ₂_ η (id₂ {a} {a}) ≅ η
  hIdL₂' {a} {b} {η = η} = het-help (η ∘ₕ₂ (id₂ {a} {a})) η (sym hIdL₁) (sym hIdL₁) hIdL₂
  
  hIdR₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
        → id₂ {b} {b} ∘ₕ₂ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  hIdR₂ = horizontalIdR₂
  
  hIdR₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₂ {b} {b} ∘ₕ₂ η ≅ η
  hIdR₂' {a} {b} {η = η} = het-help (id₂ {b} {b} ∘ₕ₂ η) η (sym hIdR₁) (sym hIdR₁) hIdR₂
  
  hAssoc₁ : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
          → h ∘ₕ (g ∘ₕ f) ≡ (h ∘ₕ g) ∘ₕ f
  hAssoc₁ = horizontalAssoc₁

  hAssoc₂ : {a b c d : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
          → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
          → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ∘ₕ₂ θ) ∘ₕ₂ ι)
  hAssoc₂ = horizontalAssoc₂
  
  hAssoc₂' : {a b c d : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
          → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
          → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≅ (η ∘ₕ₂ θ) ∘ₕ₂ ι
  hAssoc₂' {η = η} {θ} {ι} = het-help (η ∘ₕ₂ (θ ∘ₕ₂ ι)) ((η ∘ₕ₂ θ) ∘ₕ₂ ι) (sym hAssoc₁) (sym hAssoc₁) hAssoc₂
  
  whiskerLeftId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} 
                → id₂ {f = g} ◁ f ≡ id₂ {f = g ∘ₕ f}
  whiskerLeftId₁ = Functor.id comp
  
  whiskerRightId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c}
                 → g ▷ id₂ {f = f} ≡ id₂ {f = g ∘ₕ f}
  whiskerRightId₁ = Functor.id comp
  
  whiskerRightId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  whiskerRightId₂ = horizontalIdL₂
  
  whiskerRightId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≅ η
  whiskerRightId₂' {a} {b} {η = η} = het-help (η ◁ id₁ {a}) (η) (sym hIdL₁) (sym hIdL₁) whiskerRightId₂
  
  whiskerLeftId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  whiskerLeftId₂ = horizontalIdR₂

  whiskerLeftId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≅ η
  whiskerLeftId₂' {a} {b} {η = η} = het-help (id₁ {b} ▷ η) (η) (sym hIdR₁) (sym hIdR₁) whiskerLeftId₂
  
  whiskerRightDist : {a b c : Cell₀} {f : Cell₁ a b} {g h i : Cell₁ b c} {η : Cell₂ g h} {θ : Cell₂ h i}
                  → (θ ◁ f) ∘ᵥ (η ◁ f) ≡ (θ ∘ᵥ η) ◁ f
  whiskerRightDist {a} {b} {c} {f} {η = η} {θ} = 
    let _∘bc_ = Category._∘_ (HomCat b c)
    in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (θ ∘bc η , X)) vIdL)

  whiskerLeftDist : {a b c : Cell₀} {f g h : Cell₁ a b} {i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ g h}
                   → (i ▷ θ) ∘ᵥ (i ▷ η) ≡ i ▷ (θ ∘ᵥ η)
  whiskerLeftDist {a} {b} {c} {η = η} {θ} = 
    let _∘ab_ = Category._∘_ (HomCat a b)
    in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (X , θ ∘ab η)) vIdL)
  
  
  whiskerCoher1 : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                 → η ◁ (g ∘ₕ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ◁ g) ◁ f)
  whiskerCoher1 = whiskerCoher1'

  whiskerCoher1-het : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                    → η ◁ (g ∘ₕ f) ≅ (η ◁ g) ◁ f
  whiskerCoher1-het {f = f} {g} {η = η} = het-help (η ◁ (g ∘ₕ f)) ((η ◁ g) ◁ f) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher1
  
  whiskerCoher2 : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                → i ▷ (η ◁ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ▷ η) ◁ f)
  whiskerCoher2 = whiskerCoher2'
  
  whiskerCoher2-het : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                    → i ▷ (η ◁ f) ≅ (i ▷ η) ◁ f
  whiskerCoher2-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (η ◁ f)) ((i ▷ η) ◁ f) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher2
  
  whiskerCoher3 : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                → i ▷ (h ▷ η) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ∘ₕ h) ▷ η)
  whiskerCoher3 = whiskerCoher3'
  
  whiskerCoher3-het : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                    → i ▷ (h ▷ η) ≅ (i ∘ₕ h) ▷ η
  whiskerCoher3-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (h ▷ η)) ((i ∘ₕ h) ▷ η) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher3

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
  associator {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ refl (hAssoc₁ {a} {b} {c} {d} {f} {g} {h}) (id₂ {a} {d} {h ∘ₕ (g ∘ₕ f)})

  associatorInv : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                → Cell₂ ((h ∘ₕ g) ∘ₕ f) (h ∘ₕ (g ∘ₕ f)) 
  associatorInv {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ (hAssoc₁ {a} {b} {c} {d} {f} {g} {h}) refl (id₂ {a} {d} {h ∘ₕ (g ∘ₕ f)})

  associatorId : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
               → associator {a} {b} {c} {d} {f = f} {g} {h} ∘ᵥ associatorInv {a} {b} {c} {d} {f = f} {g} {h} ≡ id₂
  associatorId = trans (substComp₁ hAssoc₁) vIdR
  
  associatorId' : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                → associatorInv {a} {b} {c} {d} {f = f} {g} {h} ∘ᵥ associator {a} {b} {c} {d} {f = f} {g} {h} ≡ id₂
  associatorId' = trans (substComp₂ hAssoc₁) vIdR
  
  α : {a b c d : Cell₀} 
    → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
    → Cell₂ (h ∘ₕ (g ∘ₕ f)) ((h ∘ₕ g) ∘ₕ f)
  α {a} {b} {c} {d} f g h = associator {a} {b} {c} {d} {f = f} {g} {h}
  
  α' : {a b c d : Cell₀} 
     → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
     → Cell₂ ((h ∘ₕ g) ∘ₕ f) (h ∘ₕ (g ∘ₕ f)) 
  α' {a} {b} {c} {d} f g h = associatorInv {a} {b} {c} {d} {f = f} {g} {h}
  
  private
    compᵥ-cong₂ : {a b : Cell₀} {f g h i j k : Cell₁ a b} {ι : Cell₂ f g} {η : Cell₂ g h} {γ : Cell₂ i j} {θ : Cell₂ j k}
                → f ≡ i → g ≡ j → h ≡ k
                → η ≅ θ → ι ≅ γ
                → η ∘ᵥ ι ≅ θ ∘ᵥ γ
    compᵥ-cong₂ refl refl refl refl refl = refl
    
    subst-swap : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {ι : Cell₂ h i} 
               → (p : f ≡ h) → (q : g ≡ i)
               → subst₂ Cell₂ (sym p) (sym q) ι ≡ η → ι ≡ subst₂ Cell₂ p q η
    subst-swap refl refl refl = refl
    
    subst-swap' : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {ι : Cell₂ h i} 
               → (p : h ≡ f) → (q : i ≡ g)
               → subst₂ Cell₂ p q ι ≡ η → ι ≡ subst₂ Cell₂ (sym p) (sym q) η
    subst-swap' refl refl refl = refl
  
  left-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([ id₁ {b} ,-] comp {a} {b} {b}) Id[ HomCat a b ]
  left-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation ρ natural) (λ x → isomorphism (ρ' x) rUnitorId rUnitorId')
    where
      _∘HC_ = _∘_ (HomCat a b)
      
      natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
              → η ∘ᵥ ρ f ≡ ρ g ∘ᵥ (id₁ ▷ η)
      natural {f} {g} {η} = ≅-to-≡ $ hbegin
        η ∘ᵥ ρ f 
          ≅⟨ compᵥ-cong₂ hIdR₁ refl refl refl (het-help (ρ f) id₂ (sym hIdR₁) refl refl) ⟩ 
        η ∘ᵥ id₂
          ≅⟨ ≡-to-≅ vIdL ⟩ 
        η
          ≅⟨ ≡-to-≅ (sym vIdR) ⟩ 
        id₂ ∘ᵥ η
          ≅⟨ compᵥ-cong₂ (sym hIdR₁) (sym hIdR₁) refl (het-help id₂ (ρ g) hIdR₁ refl (subst-swap {η = ρ g} hIdR₁ refl refl)) (hsym whiskerLeftId₂') ⟩ 
        ρ g ∘ᵥ (id₁ ▷ η) ∎h

  right-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([-, id₁ {a} ] comp {a} {a} {b}) Id[ HomCat a b ]
  right-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation λ' natural) (λ x → isomorphism (λ'' x) lUnitorId lUnitorId')
    where
      natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
              → η ∘ᵥ λ' f ≡ λ' g ∘ᵥ (η ◁ id₁)
      natural {f} {g} {η} = ≅-to-≡ $ hbegin
        η ∘ᵥ λ' f 
          ≅⟨ compᵥ-cong₂ hIdL₁ refl refl refl (het-help (λ' f) id₂ (sym hIdL₁) refl refl) ⟩
        η ∘ᵥ id₂
          ≅⟨ ≡-to-≅ vIdL ⟩
        η
          ≅⟨ ≡-to-≅ (sym vIdR) ⟩
        id₂ ∘ᵥ η
          ≅⟨ compᵥ-cong₂ (sym hIdL₁) (sym hIdL₁) refl (het-help id₂ (λ' g) hIdL₁ refl (subst-swap hIdL₁ refl refl)) (hsym whiskerRightId₂') ⟩
        λ' g ∘ᵥ (η ◁ id₁) ∎h
  
  open Theory.Triple.Triple
  
  associator-iso : {a b c d : Cell₀} → NaturalIsomorphism [ biAssocFunctorL (comp {b} {c} {d}) (comp {a} {b} {d}) ]∘[ assocFunctorL ] 
                                                          [ biAssocFunctorR (comp {a} {c} {d}) (comp {a} {b} {c}) ]∘[ assocFunctorR ]
  associator-iso {a} {b} {c} {d} = naturalIsomorphism (naturalTransformation (λ x → α' (proj₃ x) (proj₂ x) (proj₁ x)) natural) (λ x → isomorphism (α (proj₃ x) (proj₂ x) (proj₁ x)) associatorId' associatorId)
    where
      _∘HC_ = _∘_ (HomCat a d)
      
      natural : {f g : Obj (HomCat c d ×C HomCat b c ×C HomCat a b)} {η : Hom (HomCat c d ×C HomCat b c ×C HomCat a b) f g} 
              → (proj₁ η ∘ₕ₂ (proj₂ η ∘ₕ₂ proj₃ η)) ∘ᵥ α' (proj₃ f) (proj₂ f) (proj₁ f)
              ≡ α' (proj₃ g) (proj₂ g) (proj₁ g) ∘ᵥ ((proj₁ η ∘ₕ₂ proj₂ η) ∘ₕ₂ proj₃ η) -- [ [ biAssocFunctorL comp comp ]∘[ assocFunctorL ] ]₁ η
      natural {f ,' f' ,' f''} {g ,' g' ,' g''} {η ,' η' ,' η''} = ≅-to-≡ $ hbegin
        (η ∘ₕ₂ (η' ∘ₕ₂ η'')) ∘ᵥ α' f'' f' f
          ≅⟨ compᵥ-cong₂ (sym hAssoc₁) refl refl refl (het-help (α' f'' f' f) id₂ hAssoc₁ refl refl) ⟩
        (η ∘ₕ₂ (η' ∘ₕ₂ η'')) ∘ᵥ id₂
          ≅⟨ ≡-to-≅ vIdL ⟩
        η ∘ₕ₂ (η' ∘ₕ₂ η'')
          ≅⟨ ≡-to-≅ (sym vIdR) ⟩
        id₂ ∘ᵥ (η ∘ₕ₂ (η' ∘ₕ₂ η''))
          ≅⟨ compᵥ-cong₂ hAssoc₁ hAssoc₁ refl (het-help id₂ (α' g'' g' g) (sym hAssoc₁) refl (subst-swap' hAssoc₁ refl refl)) hAssoc₂' ⟩
        α' g'' g' g ∘ᵥ ((η ∘ₕ₂ η') ∘ₕ₂ η'') ∎h
  
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
      ; compose = refl
      }
    
    id₁ : {a : ⊤} → Obj (HomCat a a)
    id₁ {tt} = tt

⊤-TwoCat = unitStrictTwoCategory

StrictTwoCategory→Category : ∀ {ℓ₀ ℓ₁ ℓ₂} → StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} → Category {ℓ₀} {ℓ₁}
StrictTwoCategory→Category TwoCat = record
  { Obj = StrictTwoCategory.Cell₀ TwoCat
  ; Hom = StrictTwoCategory.Cell₁ TwoCat
  ; _∘_ = λ f g → [ StrictTwoCategory.comp TwoCat ]₀ (f , g)
  ; id = StrictTwoCategory.id₁ TwoCat
  ; assoc = StrictTwoCategory.horizontalAssoc₁ TwoCat
  ; left-id = StrictTwoCategory.horizontalIdL₁ TwoCat
  ; right-id = StrictTwoCategory.horizontalIdR₁ TwoCat
  } 
