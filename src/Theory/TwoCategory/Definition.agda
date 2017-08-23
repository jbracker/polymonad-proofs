
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; subst to hsubst ; subst₂ to hsubst₂ ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

-- Local
open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition hiding ( category )
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Application
open import Theory.Functor.Association
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.TwoCategory.Definition where

open Theory.Functor.Application.BiFunctor
open Theory.Functor.Association.Triple
open Theory.Functor.Association.BiFunctor

-------------------------------------------------------------------------------
-- Definition of 2-Categories
-------------------------------------------------------------------------------

open Category hiding ( left-id ; right-id ; assoc ) renaming ( id to idC )

record StrictTwoCategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    -- Names and structure base on: https://ncatlab.org/nlab/show/strict+2-category
    --                              https://ncatlab.org/nlab/show/bicategory
    -- Definition from "Categorification" by John C. Baez (1998)
    
    Cell₀ : Set ℓ₀
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

  
  Cell₁ : Cell₀ → Cell₀ → Set ℓ₁
  Cell₁ a b = Obj (HomCat a b)
  
  Cell₂ : {a b : Cell₀} → (f g : Cell₁ a b) → Set ℓ₂
  Cell₂ {a} {b} f g = Hom (HomCat a b) f g  

  field
    --                       (b c × a b ↦ a c)
    comp : {a b c : Cell₀} → Functor (HomCat b c ×C HomCat a b) (HomCat a c) 
    id₁  : {a : Cell₀} → Cell₁ a a
  
  -- Horizontal composition
  _∘ₕ_ : {a b c : Cell₀} → Cell₁ b c → Cell₁ a b → Cell₁ a c
  _∘ₕ_ f g = [ comp ]₀ (f , g)
  
  id₂ : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f f
  id₂ {a} {b} = Category.id (HomCat a b)
  
  field
    horizontalAssoc₁ : {a b c d : Cell₀} 
                     → {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
                     → h ∘ₕ (g ∘ₕ f) ≡ (h ∘ₕ g) ∘ₕ f

    horizontalIdL₁ : {a b : Cell₀} {f : Cell₁ a b} 
          → f ∘ₕ id₁ {a} ≡ f
    
    horizontalIdR₁ :  {a b : Cell₀} {f : Cell₁ a b} 
          → id₁ {b} ∘ₕ f ≡ f
  
  _∘ₕ₂_ : {a b c : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c}
        → Cell₂ g g' → Cell₂ f f' → Cell₂ (g ∘ₕ f) (g' ∘ₕ f')
  _∘ₕ₂_ η θ = [ comp ]₁ (η , θ)
    
  field
    horizontalIdL₂ : {a b : Cell₀} 
                   → {f g : Cell₁ a b} {η : Cell₂ f g} 
                   → η ∘ₕ₂ (id₂ {a} {a} {id₁}) ≅ η
    
    horizontalIdR₂ : {a b : Cell₀} 
                   → {f g : Cell₁ a b} {η : Cell₂ f g} 
                   → id₂ {b} {b} {id₁} ∘ₕ₂ η ≅ η
    
    horizontalAssoc₂ : {a b c d : Cell₀} 
                     → {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
                     → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
                     → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≅ (η ∘ₕ₂ θ) ∘ₕ₂ ι
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdL₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
        → f ∘ₕ id₁ {a} ≡ f
  hIdL₁ = horizontalIdL₁
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdR₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
        → id₁ {b} ∘ₕ f ≡ f
  hIdR₁ = horizontalIdR₁
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hAssoc₁ : {a b c d : Cell₀} 
          → {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
          → h ∘ₕ (g ∘ₕ f) ≡ (h ∘ₕ g) ∘ₕ f
  hAssoc₁ = horizontalAssoc₁

  
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
  
  private
    abstract
      het-to-prop : {a b : Cell₀}
                  → {f g h k : Cell₁ a b} 
                  → {η : Cell₂ f g} {θ : Cell₂ h k} 
                  → (eq₁ : h ≡ f) (eq₂ : k ≡ g) 
                  → η ≅ θ 
                  → η ≡ subst₂ (Hom (HomCat a b)) eq₁ eq₂ θ
      het-to-prop refl refl refl = refl
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  vIdL : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ {f = f} ≡ θ
  vIdL {a} {b} = Category.left-id (HomCat a b)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  vIdR : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ {f = g} ∘ᵥ θ ≡ θ
  vIdR {a} {b} = Category.right-id (HomCat a b)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  vAssoc : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {θ : Cell₂ g h} {ι : Cell₂ h i}
         → ι ∘ᵥ (θ ∘ᵥ η) ≡ (ι ∘ᵥ θ) ∘ᵥ η
  vAssoc {a} {b} = Category.assoc (HomCat a b)
    
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdL₂ : {a b : Cell₀} 
        → {f g : Cell₁ a b} {η : Cell₂ f g} 
        → η ∘ₕ₂ (id₂ {a} {a} {id₁}) ≅ η
  hIdL₂ = horizontalIdL₂
  
  abstract
    horizontalIdL₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
                    → η ∘ₕ₂ id₂ {a} {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
    horizontalIdL₂' = het-to-prop (sym hIdL₁) (sym hIdL₁) hIdL₂
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdL₂' : {a b : Cell₀} 
         → {f g : Cell₁ a b} {η : Cell₂ f g} 
         → η ∘ₕ₂ id₂ {a} {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  hIdL₂' = horizontalIdL₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdR₂ : {a b : Cell₀} 
        → {f g : Cell₁ a b} {η : Cell₂ f g} 
        → id₂ {b} {b} {id₁} ∘ₕ₂ η ≅ η
  hIdR₂ = horizontalIdR₂
  
  abstract
    horizontalIdR₂' : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                    → id₂ {b} {b} ∘ₕ₂ η ≡ subst₂ (Hom (HomCat a b)) (sym hIdR₁) (sym hIdR₁) η
    horizontalIdR₂' = het-to-prop (sym hIdR₁) (sym hIdR₁) hIdR₂
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hIdR₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
         → id₂ {b} {b} ∘ₕ₂ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  hIdR₂' = horizontalIdR₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hAssoc₂ : {a b c d : Cell₀} 
          → {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
          → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
          → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≅ (η ∘ₕ₂ θ) ∘ₕ₂ ι
  hAssoc₂ = horizontalAssoc₂

  abstract
    horizontalAssoc₂' : {a b c d : Cell₀} {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
                      → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
                      → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≡ subst₂ (Hom (HomCat a d)) (sym hAssoc₁) (sym hAssoc₁) ((η ∘ₕ₂ θ) ∘ₕ₂ ι)
    horizontalAssoc₂' = het-to-prop (sym hAssoc₁) (sym hAssoc₁) hAssoc₂
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  hAssoc₂' : {a b c d : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
           → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
           → η ∘ₕ₂ (θ ∘ₕ₂ ι) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ∘ₕ₂ θ) ∘ₕ₂ ι)
  hAssoc₂' = horizontalAssoc₂'
  
  private
    abstract
      het-help : {a b : Cell₀} 
               → {f g h k : Cell₁ a b} 
               → (η : Cell₂ f g) (ι : Cell₂ h k)
               → (p : h ≡ f) (q : k ≡ g)
               → η ≡ subst₂ Cell₂ p q ι → η ≅ ι
      het-help η ι refl refl refl = refl
    
    abstract
      compᵥ-cong₂ : {a b : Cell₀} {f g h i j k : Cell₁ a b} {ι : Cell₂ f g} {η : Cell₂ g h} {γ : Cell₂ i j} {θ : Cell₂ j k}
                  → f ≡ i → g ≡ j → h ≡ k
                  → η ≅ θ → ι ≅ γ
                  → η ∘ᵥ ι ≅ θ ∘ᵥ γ
      compᵥ-cong₂ refl refl refl refl refl = refl
    
    abstract
      compₕ-cong₂ : {a b c : Cell₀} {f g l m : Cell₁ a b} {h i j k : Cell₁ b c} {ι : Cell₂ h i} {η : Cell₂ f g} {γ : Cell₂ j k} {θ : Cell₂ l m}
                  → h ≡ j → i ≡ k → f ≡ l → g ≡ m
                  → η ≅ θ → ι ≅ γ
                  → ι ∘ₕ₂ η ≅ γ ∘ₕ₂ θ
      compₕ-cong₂ refl refl refl refl refl refl = refl
    
  private
    abstract
      subst-swap : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {ι : Cell₂ h i} 
                 → (p : f ≡ h) → (q : g ≡ i)
                 → subst₂ Cell₂ (sym p) (sym q) ι ≡ η → ι ≡ subst₂ Cell₂ p q η
      subst-swap refl refl refl = refl
    
    abstract
      subst-swap' : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {ι : Cell₂ h i} 
                  → (p : h ≡ f) → (q : i ≡ g)
                  → subst₂ Cell₂ p q ι ≡ η → ι ≡ subst₂ Cell₂ (sym p) (sym q) η
      subst-swap' refl refl refl = refl
    
    abstract
      subst-swap'' : {a b : Cell₀} {f g : Cell₁ a b} → (p : f ≡ g) → subst₂ Cell₂ p refl id₂ ≡ subst₂ Cell₂ refl (sym p) id₂
      subst-swap'' refl = refl
    
  private
    abstract
      subst-id : {a b : Cell₀} {f g h : Cell₁ a b} 
               → (p : f ≡ g) → (q : f ≡ h)
               → subst₂ Cell₂ p q id₂ ≅ id₂ {f = h}
      subst-id refl refl = refl
    
  abstract
    id≅id : {a b : Cell₀} {f g : Cell₁ a b} → f ≡ g → id₂ {f = f} ≅ id₂ {f = g}
    id≅id refl = refl

  abstract
    id∘ₕ₂id≡id : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} → id₂ {f = g} ∘ₕ₂ id₂ {f = f} ≡ id₂ {f = g ∘ₕ f}
    id∘ₕ₂id≡id {a} {b} {c} {f} {g} = Functor.id comp
  
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
    abstract
      substComp₁ : {a b : Cell₀} {f g : Cell₁ a b}
                 → (eq : g ≡ f)
                 → (subst₂ Cell₂ refl eq id₂) ∘ᵥ (subst₂ Cell₂ eq refl id₂) ≡ id₂ ∘ᵥ id₂
      substComp₁ refl = refl
  
    abstract
      substComp₂ : {a b : Cell₀} {f g : Cell₁ a b}
                 → (eq : g ≡ f)
                 → (subst₂ Cell₂ eq refl id₂) ∘ᵥ (subst₂ Cell₂ refl eq id₂) ≡ id₂ ∘ᵥ id₂
      substComp₂ refl = refl
  
  abstract
    lUnitorId : {a b : Cell₀} {f : Cell₁ a b} 
              → lUnitor {a} {b} {f} ∘ᵥ lUnitorInv {a} {b} {f} ≡ id₂ {f = f}
    lUnitorId {a} {b} {f} = trans (substComp₂ (sym hIdL₁)) vIdL
  
  abstract
    lUnitorId' : {a b : Cell₀} {f : Cell₁ a b} 
               → lUnitorInv {a} {b} {f} ∘ᵥ lUnitor {a} {b} {f} ≡ id₂
    lUnitorId' {a} {b} {f} = trans (substComp₁ (sym hIdL₁)) vIdL
  
  abstract
    rUnitorId : {a b : Cell₀} {f : Cell₁ a b} 
              → rUnitor {a} {b} {f} ∘ᵥ rUnitorInv {a} {b} {f} ≡ id₂ {f = f}
    rUnitorId {a} {b} {f} = trans (substComp₂ (sym hIdR₁)) vIdR
  
  abstract
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

  abstract
    associatorId : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                 → associator {a} {b} {c} {d} {f = f} {g} {h} ∘ᵥ associatorInv {a} {b} {c} {d} {f = f} {g} {h} ≡ id₂
    associatorId = trans (substComp₁ hAssoc₁) vIdR
  
  abstract
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
  
  
  left-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([ id₁ {b} ,-] comp {a} {b} {b}) Id[ HomCat a b ]
  left-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation ρ natural) (λ x → isomorphism (ρ' x) rUnitorId rUnitorId')
    where
      _∘HC_ = _∘_ (HomCat a b)
      
      abstract
        natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                → η ∘ᵥ ρ f ≡ ρ g ∘ᵥ (id₂ {b} {b} ∘ₕ₂ η)
        natural {f} {g} {η} = ≅-to-≡ $ hbegin
          η ∘ᵥ ρ f 
            ≅⟨ compᵥ-cong₂ hIdR₁ refl refl refl (het-help (ρ f) id₂ (sym hIdR₁) refl refl) ⟩ 
          η ∘ᵥ id₂
            ≅⟨ ≡-to-≅ vIdL ⟩ 
          η
            ≅⟨ ≡-to-≅ (sym vIdR) ⟩ 
          id₂ ∘ᵥ η
            ≅⟨ compᵥ-cong₂ (sym hIdR₁) (sym hIdR₁) refl (het-help id₂ (ρ g) hIdR₁ refl (subst-swap {η = ρ g} hIdR₁ refl refl)) (hsym hIdR₂) ⟩ 
          ρ g ∘ᵥ (id₂ {b} {b} ∘ₕ₂ η) ∎h

  right-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([-, id₁ {a} ] comp {a} {a} {b}) Id[ HomCat a b ]
  right-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation λ' natural) (λ x → isomorphism (λ'' x) lUnitorId lUnitorId')
    where
      abstract
        natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                → η ∘ᵥ λ' f ≡ λ' g ∘ᵥ (η ∘ₕ₂ id₂ {a} {a})
        natural {f} {g} {η} = ≅-to-≡ $ hbegin
          η ∘ᵥ λ' f 
            ≅⟨ compᵥ-cong₂ hIdL₁ refl refl refl (het-help (λ' f) id₂ (sym hIdL₁) refl refl) ⟩
          η ∘ᵥ id₂
            ≅⟨ ≡-to-≅ vIdL ⟩
          η
            ≅⟨ ≡-to-≅ (sym vIdR) ⟩
          id₂ ∘ᵥ η
            ≅⟨ compᵥ-cong₂ (sym hIdL₁) (sym hIdL₁) refl (het-help id₂ (λ' g) hIdL₁ refl (subst-swap hIdL₁ refl refl)) (hsym hIdL₂) ⟩
          λ' g ∘ᵥ (η ∘ₕ₂ id₂ {a} {a}) ∎h
  
  open Theory.Triple.Triple
  
  associator-iso : {a b c d : Cell₀} → NaturalIsomorphism [ biAssocFunctorL (comp {b} {c} {d}) (comp {a} {b} {d}) ]∘[ assocFunctorL ] 
                                                          [ biAssocFunctorR (comp {a} {c} {d}) (comp {a} {b} {c}) ]∘[ assocFunctorR ]
  associator-iso {a} {b} {c} {d} = naturalIsomorphism (naturalTransformation (λ x → α' (proj₃ x) (proj₂ x) (proj₁ x)) natural) (λ x → isomorphism (α (proj₃ x) (proj₂ x) (proj₁ x)) associatorId' associatorId)
    where
      _∘HC_ = _∘_ (HomCat a d)
      
      abstract
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
            ≅⟨ compᵥ-cong₂ hAssoc₁ hAssoc₁ refl (het-help id₂ (α' g'' g' g) (sym hAssoc₁) refl (subst-swap' hAssoc₁ refl refl)) hAssoc₂ ⟩
          α' g'' g' g ∘ᵥ ((η ∘ₕ₂ η') ∘ₕ₂ η'') ∎h
  
  abstract
    triangle-id : {a b c : Cell₀} (f : Cell₁ a b) (g : Cell₁ b c) 
                → λ' g ∘ₕ₂ id₂ ≡ (id₂ ∘ₕ₂ ρ f) ∘ᵥ α' f id₁ g
    triangle-id f g = ≅-to-≡ $ hbegin
      λ' g ∘ₕ₂ id₂ 
        ≅⟨ compₕ-cong₂ hIdL₁ refl refl refl refl (het-help (λ' g) id₂ (sym hIdL₁) refl refl) ⟩
      id₂ {f = g} ∘ₕ₂ id₂ {f = f}
        ≅⟨ compₕ-cong₂ refl refl (sym hIdR₁) (sym hIdR₁) (id≅id (sym hIdR₁)) refl ⟩
      id₂ {f = g} ∘ₕ₂ id₂ {f = id₁ ∘ₕ f}
        ≅⟨ ≡-to-≅ (sym vIdL) ⟩
      (id₂ ∘ₕ₂ id₂) ∘ᵥ id₂
        ≅⟨ compᵥ-cong₂ hAssoc₁ refl (cong (λ X → g ∘ₕ X) hIdR₁) 
                       (compₕ-cong₂ refl refl refl hIdR₁ (het-help id₂ (ρ f) refl (sym hIdR₁) (subst-swap refl (sym hIdR₁) p)) refl) 
                       (het-help id₂ (α' f id₁ g) (sym hAssoc₁) refl (subst-swap' hAssoc₁ refl refl)) ⟩
      (id₂ ∘ₕ₂ ρ f) ∘ᵥ α' f id₁ g ∎h
      where
        abstract
          p : subst₂ Cell₂ refl (sym (sym hIdR₁)) id₂ ≡ ρ f
          p = ≅-to-≡ $ hbegin
            subst₂ Cell₂ refl (sym (sym hIdR₁)) id₂ 
              ≅⟨ subst-id refl (sym (sym hIdR₁)) ⟩
            id₂ {f = f}
              ≅⟨ hsym (subst-id (sym hIdR₁) refl) ⟩
            subst₂ Cell₂ (sym hIdR₁) refl id₂
              ≅⟨ refl ⟩
            ρ f ∎h
  
  abstract
    pentagon-id : {a b c d e : Cell₀} 
                → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d) (k : Cell₁ d e)
                → (id₂ {f = k} ∘ₕ₂ α' f g h) ∘ᵥ (α' f (h ∘ₕ g) k ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f}))
                ≡ α' (g ∘ₕ f) h k ∘ᵥ α' f g (k ∘ₕ h)
    pentagon-id f g h k = ≅-to-≡ $ hbegin
      (id₂ {f = k} ∘ₕ₂ α' f g h) ∘ᵥ (α' f (h ∘ₕ g) k ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f}))
        ≅⟨ compᵥ-cong₂ refl refl (cong (λ X → k ∘ₕ X) hAssoc₁) (compₕ-cong₂ refl refl refl hAssoc₁ (het-help (α' f g h) id₂ refl (sym hAssoc₁) (subst-swap'' hAssoc₁)) refl) refl ⟩
      (id₂ {f = k} ∘ₕ₂ id₂ {f = (h ∘ₕ g) ∘ₕ f}) ∘ᵥ (α' f (h ∘ₕ g) k ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f}))
        ≅⟨ compᵥ-cong₂ refl refl refl (≡-to-≅ id∘ₕ₂id≡id) refl ⟩
      (id₂ {f = k ∘ₕ ((h ∘ₕ g) ∘ₕ f)}) ∘ᵥ (α' f (h ∘ₕ g) k ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f}))
        ≅⟨ ≡-to-≅ vIdR ⟩
      α' f (h ∘ₕ g) k ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f})
        ≅⟨ compᵥ-cong₂ refl refl hAssoc₁ (het-help (α' f (h ∘ₕ g) k) id₂ refl (sym hAssoc₁) (subst-swap'' hAssoc₁)) refl ⟩
      id₂ {f = (k ∘ₕ (h ∘ₕ g)) ∘ₕ f} ∘ᵥ (α' g h k ∘ₕ₂ id₂ {f = f})
        ≅⟨ ≡-to-≅ vIdR ⟩
      α' g h k ∘ₕ₂ id₂ {f = f}
        ≅⟨ compₕ-cong₂ refl hAssoc₁ refl refl refl (het-help (α' g h k) id₂ refl (sym hAssoc₁) (subst-swap'' hAssoc₁)) ⟩
      id₂ {f = (k ∘ₕ h) ∘ₕ g} ∘ₕ₂ id₂ {f = f}
        ≅⟨ ≡-to-≅ id∘ₕ₂id≡id ⟩
      id₂ {f = ((k ∘ₕ h) ∘ₕ g) ∘ₕ f}
        ≅⟨ id≅id (sym hAssoc₁) ⟩
      id₂ {f = (k ∘ₕ h) ∘ₕ (g ∘ₕ f)}
        ≅⟨ ≡-to-≅ (sym vIdR) ⟩
      id₂ {f = (k ∘ₕ h) ∘ₕ (g ∘ₕ f)} ∘ᵥ id₂ {f = (k ∘ₕ h) ∘ₕ (g ∘ₕ f)} 
        ≅⟨ compᵥ-cong₂ hAssoc₁ refl (sym hAssoc₁) (het-help id₂ (α' (g ∘ₕ f) h k) refl hAssoc₁ 
                       (subst-swap refl hAssoc₁ (sym (subst-swap'' hAssoc₁)))) 
                       (het-help id₂ (α' f g (k ∘ₕ h)) (sym hAssoc₁) refl (subst-swap' hAssoc₁ refl refl)) ⟩
      α' (g ∘ₕ f) h k ∘ᵥ α' f g (k ∘ₕ h) ∎h
    
  abstract
    interchange : {a b c : Cell₀} 
                → {x y z : Obj (HomCat a b)} {x' y' z' : Obj (HomCat b c)}
                → (f : Hom (HomCat a b) x y) (f' : Hom (HomCat b c) x' y') (g : Hom (HomCat a b) y z) (g' : Hom (HomCat b c) y' z')
                → (g' ∘ᵥ f') ∘ₕ₂ (g ∘ᵥ f) ≡ (g' ∘ₕ₂ g) ∘ᵥ (f' ∘ₕ₂ f)
    interchange {x} {y} {z} {x'} {y'} {z'} f f' g g' = begin
      [ comp ]₁ ((g' ∘ᵥ f') , (g ∘ᵥ f)) 
        ≡⟨ Functor.compose comp ⟩
      ([ comp ]₁ (g' , g)) ∘ᵥ ([ comp ]₁ (f' , f)) ∎
  
  category : Category {ℓ₀} {ℓ₁}
  category = Category.category Cell₀ Cell₁ _∘ₕ_ id₁ hAssoc₁ hIdR₁ hIdL₁
  
  whiskerCoher1' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h i : Obj (HomCat c d)} {η : Hom (HomCat c d) h i}
                 → η ∘ₕ₂ id₂ {a} {c}
                 ≡ subst₂ Cell₂ (sym (horizontalAssoc₁ {f = f} {g = g})) (sym horizontalAssoc₁) (((η ∘ₕ₂ id₂ {b} {c})) ∘ₕ₂ id₂ {a} {b})
  whiskerCoher1' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym (horizontalAssoc₁ {f = f} {g = g})) (sym horizontalAssoc₁) (htrans (hcong (λ X → η ∘ₕ₂ X) (hsym (≡-to-≅ id∘ₕ₂id≡id))) hAssoc₂)
  
  whiskerCoher2' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g h : Obj (HomCat b c)} {i : Obj (HomCat c d)} {η : Hom (HomCat b c) g h} 
                 → id₂ {f = i} ∘ₕ₂ (η ∘ₕ₂ id₂ {f = f}) 
                 ≡ subst₂ Cell₂ (sym (horizontalAssoc₁ {f = f} {g = g})) (sym (horizontalAssoc₁ {f = f} {g = h})) ((id₂ {c} {d} ∘ₕ₂ η) ∘ₕ₂ id₂ {a} {b})
  whiskerCoher2' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym (horizontalAssoc₁ {f = f} {g = g})) (sym (horizontalAssoc₁ {f = f} {g = h})) hAssoc₂
  
  whiskerCoher3' : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                 → id₂ {f = i} ∘ₕ₂ (id₂ {f = h} ∘ₕ₂ η) 
                 ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) (id₂ {f = i ∘ₕ h} ∘ₕ₂ η)
  whiskerCoher3' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym hAssoc₁) (sym hAssoc₁) (htrans hAssoc₂ (hcong (λ X → X ∘ₕ₂ η) (≡-to-≅ id∘ₕ₂id≡id)))
  
  whiskerCoher4' : {a b c : Cell₀} {f g : Cell₁ a b} {h i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ h i}
                 → (id₂ {f = i} ∘ₕ₂ η) ∘ᵥ (θ ∘ₕ₂ id₂ {f = f}) ≡ (θ ∘ₕ₂ id₂ {f = g}) ∘ᵥ (id₂ {f = h} ∘ₕ₂ η)
  whiskerCoher4' {a} {b} {c} {f} {g} {h} {i} {η} {θ} = ≅-to-≡ $ hbegin
    (id₂ {f = i} ∘ₕ₂ η) ∘ᵥ (θ ∘ₕ₂ id₂ {f = f}) 
      ≅⟨ ≡-to-≅ (sym $ interchange id₂ θ η id₂) ⟩
    (id₂ {f = i} ∘ᵥ θ) ∘ₕ₂ (η ∘ᵥ id₂ {f = f}) 
      ≅⟨ hcong₂ _∘ₕ₂_ (≡-to-≅ vIdR) (≡-to-≅ vIdL) ⟩
    θ ∘ₕ₂ η
      ≅⟨ hcong₂ _∘ₕ₂_ (≡-to-≅ (sym vIdL)) (≡-to-≅ (sym vIdR)) ⟩
    (θ ∘ᵥ id₂ {f = h}) ∘ₕ₂ (id₂ {f = g} ∘ᵥ η)
      ≅⟨ ≡-to-≅ (interchange η id₂ id₂ θ) ⟩
    (θ ∘ₕ₂ id₂ {f = g}) ∘ᵥ (id₂ {f = h} ∘ₕ₂ η) ∎h
  
  abstract
    whiskerRightDist : {a b c : Cell₀} {f : Cell₁ a b} {g h i : Cell₁ b c} {η : Cell₂ g h} {θ : Cell₂ h i}
                     → (θ ◁ f) ∘ᵥ (η ◁ f) ≡ (θ ∘ᵥ η) ◁ f
    whiskerRightDist {a} {b} {c} {f} {η = η} {θ} = 
      let _∘bc_ = Category._∘_ (HomCat b c)
      in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (θ ∘bc η , X)) vIdL)
  
  abstract
    whiskerLeftDist : {a b c : Cell₀} {f g h : Cell₁ a b} {i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ g h}
                    → (i ▷ θ) ∘ᵥ (i ▷ η) ≡ i ▷ (θ ∘ᵥ η)
    whiskerLeftDist {a} {b} {c} {η = η} {θ} = 
      let _∘ab_ = Category._∘_ (HomCat a b)
      in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (X , θ ∘ab η)) vIdL)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher1 : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                → η ◁ (g ∘ₕ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((η ◁ g) ◁ f)
  whiskerCoher1 = whiskerCoher1'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher2 : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                → i ▷ (η ◁ f) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ▷ η) ◁ f)
  whiskerCoher2 = whiskerCoher2'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher3 : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                → i ▷ (h ▷ η) ≡ subst₂ Cell₂ (sym hAssoc₁) (sym hAssoc₁) ((i ∘ₕ h) ▷ η)
  whiskerCoher3 = whiskerCoher3'

  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher4 : {a b c : Cell₀} {f g : Cell₁ a b} {h i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ h i}
                → (i ▷ η) ∘ᵥ (θ ◁ f) ≡ (θ ◁ g) ∘ᵥ (h ▷ η)
  whiskerCoher4 = whiskerCoher4'
  
  abstract
    whiskerCoher1-het : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                      → η ◁ (g ∘ₕ f) ≅ (η ◁ g) ◁ f
    whiskerCoher1-het {f = f} {g} {η = η} = het-help (η ◁ (g ∘ₕ f)) ((η ◁ g) ◁ f) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher1
  
  abstract
    whiskerCoher2-het : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                      → i ▷ (η ◁ f) ≅ (i ▷ η) ◁ f
    whiskerCoher2-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (η ◁ f)) ((i ▷ η) ◁ f) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher2
  
  abstract
    whiskerCoher3-het : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                      → i ▷ (h ▷ η) ≅ (i ∘ₕ h) ▷ η
    whiskerCoher3-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (h ▷ η)) ((i ∘ₕ h) ▷ η) (sym hAssoc₁) (sym hAssoc₁) whiskerCoher3

  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} 
                 → id₂ {f = g} ◁ f ≡ id₂ {f = g ∘ₕ f}
  whiskerLeftId₁ = Functor.id comp
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c}
                  → g ▷ id₂ {f = f} ≡ id₂ {f = g ∘ₕ f}
  whiskerRightId₁ = Functor.id comp
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  whiskerRightId₂' = horizontalIdL₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≅ η
  whiskerRightId₂ {a} {b} {η = η} = het-help (η ◁ id₁ {a}) (η) (sym hIdL₁) (sym hIdL₁) whiskerRightId₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  whiskerLeftId₂' = horizontalIdR₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≅ η
  whiskerLeftId₂ {a} {b} {η = η} = het-help (id₁ {b} ▷ η) (η) (sym hIdR₁) (sym hIdR₁) whiskerLeftId₂'  

  -- END StrictTwoCategory

StrictTwoCategory→Category : ∀ {ℓ₀ ℓ₁ ℓ₂} → StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} → Category {ℓ₀} {ℓ₁}
StrictTwoCategory→Category = StrictTwoCategory.category

