
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

open Category hiding ( left-id ; right-id ; assoc ; _∘_ ) renaming ( id to idC )

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
  
  -- Normal composition of 1-cells
  _∘_ : {a b c : Cell₀} → Cell₁ b c → Cell₁ a b → Cell₁ a c
  _∘_ f g = [ comp ]₀ (f , g)
  
  id₂ : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f f
  id₂ {a} {b} = Category.id (HomCat a b)
  
  field
    assoc : {a b c d : Cell₀} 
          → {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

    left-id : {a b : Cell₀} {f : Cell₁ a b} 
            → f ∘ id₁ {a} ≡ f
    
    right-id : {a b : Cell₀} {f : Cell₁ a b} 
             → id₁ {b} ∘ f ≡ f

  -- Horizontal composition of 2-cells
  _∘ₕ_ : {a b c : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c}
        → Cell₂ g g' → Cell₂ f f' → Cell₂ (g ∘ f) (g' ∘ f')
  _∘ₕ_ η θ = [ comp ]₁ (η , θ)
    
  field
    horizontal-left-id : {a b : Cell₀} 
                       → {f g : Cell₁ a b} {η : Cell₂ f g} 
                       → η ∘ₕ (id₂ {a} {a} {id₁}) ≅ η
    
    horizontal-right-id : {a b : Cell₀} 
                        → {f g : Cell₁ a b} {η : Cell₂ f g} 
                        → id₂ {b} {b} {id₁} ∘ₕ η ≅ η
    
    horizontal-assoc : {a b c d : Cell₀} 
                     → {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
                     → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
                     → η ∘ₕ (θ ∘ₕ ι) ≅ (η ∘ₕ θ) ∘ₕ ι
  
  -- Vertical composition of 2-cells
  _∘ᵥ_ : {a b : Cell₀} {f g h : Cell₁ a b} → Cell₂ g h → Cell₂ f g → Cell₂ f h
  _∘ᵥ_ {a = a} {b = b} η θ = Category._∘_ (HomCat a b) η θ
  
  -- Right whiskering
  _▷_ : {a b c : Cell₀} {f g : Cell₁ a b} 
      → (h : Cell₁ b c) → Cell₂ f g → Cell₂ (h ∘ f) (h ∘ g)
  _▷_ {b = b} {c = c} h η = id₂ {b} {c} ∘ₕ η

  -- Left whiskering
  _◁_ : {a b c : Cell₀} {f g : Cell₁ b c} 
      → Cell₂ f g → (h : Cell₁ a b) → Cell₂ (f ∘ h) (g ∘ h)
  _◁_ {a = a} {b = b} η h = η ∘ₕ id₂ {a} {b}
  
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
  vertical-left-id : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ {f = f} ≡ θ
  vertical-left-id {a} {b} = Category.left-id (HomCat a b)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  v-left-id : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ {f = f} ≡ θ
  v-left-id = vertical-left-id
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  vertical-right-id : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ {f = g} ∘ᵥ θ ≡ θ
  vertical-right-id {a} {b} = Category.right-id (HomCat a b)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  v-right-id : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ {f = g} ∘ᵥ θ ≡ θ
  v-right-id = vertical-right-id
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  vertical-assoc : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {θ : Cell₂ g h} {ι : Cell₂ h i}
         → ι ∘ᵥ (θ ∘ᵥ η) ≡ (ι ∘ᵥ θ) ∘ᵥ η
  vertical-assoc {a} {b} = Category.assoc (HomCat a b)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  v-assoc : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {θ : Cell₂ g h} {ι : Cell₂ h i}
         → ι ∘ᵥ (θ ∘ᵥ η) ≡ (ι ∘ᵥ θ) ∘ᵥ η
  v-assoc = vertical-assoc
    
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-left-id : {a b : Cell₀} 
            → {f g : Cell₁ a b} {η : Cell₂ f g} 
            → η ∘ₕ (id₂ {a} {a} {id₁}) ≅ η
  h-left-id = horizontal-left-id
  
  abstract
    horizontal-left-id' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
                    → η ∘ₕ id₂ {a} {a} ≡ subst₂ Cell₂ (sym left-id) (sym left-id) η
    horizontal-left-id' = het-to-prop (sym left-id) (sym left-id) h-left-id
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-left-id' : {a b : Cell₀} 
         → {f g : Cell₁ a b} {η : Cell₂ f g} 
         → η ∘ₕ id₂ {a} {a} ≡ subst₂ Cell₂ (sym left-id) (sym left-id) η
  h-left-id' = horizontal-left-id'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-right-id : {a b : Cell₀} 
             → {f g : Cell₁ a b} {η : Cell₂ f g} 
             → id₂ {b} {b} {id₁} ∘ₕ η ≅ η
  h-right-id = horizontal-right-id
  
  abstract
    horizontal-right-id' : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                    → id₂ {b} {b} ∘ₕ η ≡ subst₂ (Hom (HomCat a b)) (sym right-id) (sym right-id) η
    horizontal-right-id' = het-to-prop (sym right-id) (sym right-id) h-right-id
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-right-id' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
         → id₂ {b} {b} ∘ₕ η ≡ subst₂ Cell₂ (sym right-id) (sym right-id) η
  h-right-id' = horizontal-right-id'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-assoc : {a b c d : Cell₀} 
          → {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
          → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
          → η ∘ₕ (θ ∘ₕ ι) ≅ (η ∘ₕ θ) ∘ₕ ι
  h-assoc = horizontal-assoc

  abstract
    horizontal-assoc' : {a b c d : Cell₀} {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
                      → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
                      → η ∘ₕ (θ ∘ₕ ι) ≡ subst₂ (Hom (HomCat a d)) (sym assoc) (sym assoc) ((η ∘ₕ θ) ∘ₕ ι)
    horizontal-assoc' = het-to-prop (sym assoc) (sym assoc) h-assoc
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  h-assoc' : {a b c d : Cell₀} {f f' : Cell₁ a b} {g g' : Cell₁ b c} {h h' : Cell₁ c d}
           → {η : Cell₂ h h'} {θ : Cell₂ g g'} {ι : Cell₂ f f'}
           → η ∘ₕ (θ ∘ₕ ι) ≡ subst₂ Cell₂ (sym assoc) (sym assoc) ((η ∘ₕ θ) ∘ₕ ι)
  h-assoc' = horizontal-assoc'
  
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
                  → ι ∘ₕ η ≅ γ ∘ₕ θ
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
      
      subst-id' : {a b : Cell₀} {f g h : Cell₁ a b} 
                → (p : f ≡ g) → (q : f ≡ h)
                → subst₂ Cell₂ p q id₂ ≅ id₂ {f = g}
      subst-id' refl refl = refl
    
  abstract
    id≅id : {a b : Cell₀} {f g : Cell₁ a b} → f ≡ g → id₂ {f = f} ≅ id₂ {f = g}
    id≅id refl = refl

  abstract
    id∘ₕid≡id : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} → id₂ {f = g} ∘ₕ id₂ {f = f} ≡ id₂ {f = g ∘ f}
    id∘ₕid≡id {a} {b} {c} {f} {g} = Functor.id comp
  
  -- Unitors
  lUnitor : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ (f ∘ id₁) f
  lUnitor {a} {b} {f} = subst₂ Cell₂ (sym $ left-id {a} {b} {f}) refl (id₂ {a} {b})

  lUnitorInv : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f (f ∘ id₁)
  lUnitorInv {a} {b} {f} = subst₂ Cell₂ refl (sym left-id) (id₂ {a} {b})
  
  λ' : {a b : Cell₀} → (f : Cell₁ a b) → Cell₂ (f ∘ id₁) f
  λ' {a} {b} f = lUnitor {a} {b} {f}
  
  λ'' : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ f (f ∘ id₁)
  λ'' {a} {b} f = lUnitorInv {a} {b} {f}

  λ'≅id₂ : {a b : Cell₀} → (f : Cell₁ a b) → λ' f ≅ id₂ {f = f}
  λ'≅id₂ {a} {b} f = subst-id (sym $ left-id {a} {b} {f}) refl
  
  λ''≅id₂ : {a b : Cell₀} → (f : Cell₁ a b) → λ'' f ≅ id₂ {f = f}
  λ''≅id₂ {a} {b} f = subst-id' refl (sym left-id)
  
  rUnitor : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ (id₁ ∘ f) f
  rUnitor {a} {b} {f} = subst₂ Cell₂ (sym $ right-id {a} {b} {f}) refl (id₂ {a} {b})
  
  rUnitorInv : {a b : Cell₀} {f : Cell₁ a b} → Cell₂ f (id₁ ∘ f)
  rUnitorInv {a} {b} {f} = subst₂ Cell₂ refl (sym $ right-id {a} {b} {f}) (id₂ {a} {b})

  ρ : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ (id₁ ∘ f) f
  ρ {a} {b} f = rUnitor {a} {b} {f}
  
  ρ' : {a b : Cell₀} (f : Cell₁ a b) → Cell₂ f (id₁ ∘ f)
  ρ' {a} {b} f = rUnitorInv {a} {b} {f}
  
  ρ≅id₂ : {a b : Cell₀} → (f : Cell₁ a b) → ρ f ≅ id₂ {f = f}
  ρ≅id₂ {a} {b} f = subst-id (sym $ right-id {a} {b} {f}) refl
  
  ρ'≅id₂ : {a b : Cell₀} → (f : Cell₁ a b) → ρ' f ≅ id₂ {f = f}
  ρ'≅id₂ {a} {b} f = subst-id' refl (sym $ right-id {a} {b} {f})
  
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
    lUnitorId {a} {b} {f} = trans (substComp₂ (sym left-id)) v-left-id
  
  abstract
    lUnitorId' : {a b : Cell₀} {f : Cell₁ a b} 
               → lUnitorInv {a} {b} {f} ∘ᵥ lUnitor {a} {b} {f} ≡ id₂
    lUnitorId' {a} {b} {f} = trans (substComp₁ (sym left-id)) v-left-id
  
  abstract
    rUnitorId : {a b : Cell₀} {f : Cell₁ a b} 
              → rUnitor {a} {b} {f} ∘ᵥ rUnitorInv {a} {b} {f} ≡ id₂ {f = f}
    rUnitorId {a} {b} {f} = trans (substComp₂ (sym right-id)) v-right-id
  
  abstract
    rUnitorId' : {a b : Cell₀} {f : Cell₁ a b} 
               → rUnitorInv {a} {b} {f} ∘ᵥ rUnitor {a} {b} {f} ≡ id₂
    rUnitorId' {a} {b} {f} = trans (substComp₁ (sym right-id)) v-right-id
  
  -- Associators
  associator : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
             → Cell₂ (h ∘ (g ∘ f)) ((h ∘ g) ∘ f)
  associator {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ refl (assoc {a} {b} {c} {d} {f} {g} {h}) (id₂ {a} {d} {h ∘ (g ∘ f)})

  associatorInv : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                → Cell₂ ((h ∘ g) ∘ f) (h ∘ (g ∘ f)) 
  associatorInv {a} {b} {c} {d} {f} {g} {h} = subst₂ Cell₂ (assoc {a} {b} {c} {d} {f} {g} {h}) refl (id₂ {a} {d} {h ∘ (g ∘ f)})

  abstract
    associatorId : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                 → associator {a} {b} {c} {d} {f = f} {g} {h} ∘ᵥ associatorInv {a} {b} {c} {d} {f = f} {g} {h} ≡ id₂
    associatorId = trans (substComp₁ assoc) v-right-id
  
  abstract
    associatorId' : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d}
                  → associatorInv {a} {b} {c} {d} {f = f} {g} {h} ∘ᵥ associator {a} {b} {c} {d} {f = f} {g} {h} ≡ id₂
    associatorId' = trans (substComp₂ assoc) v-right-id
  
  α : {a b c d : Cell₀} 
    → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
    → Cell₂ (h ∘ (g ∘ f)) ((h ∘ g) ∘ f)
  α {a} {b} {c} {d} f g h = associator {a} {b} {c} {d} {f = f} {g} {h}
  
  α' : {a b c d : Cell₀} 
     → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
     → Cell₂ ((h ∘ g) ∘ f) (h ∘ (g ∘ f)) 
  α' {a} {b} {c} {d} f g h = associatorInv {a} {b} {c} {d} {f = f} {g} {h}
  
  α≅id₂ : {a b c d : Cell₀} 
        → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
        → α f g h ≅ id₂ {f = (h ∘ g) ∘ f}
  α≅id₂ {a} {b} {c} {d} f g h = subst-id refl (assoc {a} {b} {c} {d} {f} {g} {h})
  
  α'≅id₂ : {a b c d : Cell₀} 
        → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d)
        → α' f g h ≅ id₂ {f = (h ∘ g) ∘ f}
  α'≅id₂ {a} {b} {c} {d} f g h = subst-id' (assoc {a} {b} {c} {d} {f} {g} {h}) refl
  
  left-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([ id₁ {b} ,-] comp {a} {b} {b}) Id[ HomCat a b ]
  left-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation ρ natural) (λ x → isomorphism (ρ' x) rUnitorId rUnitorId')
    where
      _∘HC_ = Category._∘_ (HomCat a b)
      
      abstract
        natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                → η ∘ᵥ ρ f ≡ ρ g ∘ᵥ (id₂ {b} {b} ∘ₕ η)
        natural {f} {g} {η} = ≅-to-≡ $ hbegin
          η ∘ᵥ ρ f 
            ≅⟨ compᵥ-cong₂ right-id refl refl refl (het-help (ρ f) id₂ (sym right-id) refl refl) ⟩ 
          η ∘ᵥ id₂
            ≅⟨ ≡-to-≅ v-left-id ⟩ 
          η
            ≅⟨ ≡-to-≅ (sym v-right-id) ⟩ 
          id₂ ∘ᵥ η
            ≅⟨ compᵥ-cong₂ (sym right-id) (sym right-id) refl (het-help id₂ (ρ g) right-id refl (subst-swap {η = ρ g} right-id refl refl)) (hsym h-right-id) ⟩ 
          ρ g ∘ᵥ (id₂ {b} {b} ∘ₕ η) ∎h

  right-unitor-iso : {a b : Cell₀} → NaturalIsomorphism ([-, id₁ {a} ] comp {a} {a} {b}) Id[ HomCat a b ]
  right-unitor-iso {a} {b} = naturalIsomorphism (naturalTransformation λ' natural) (λ x → isomorphism (λ'' x) lUnitorId lUnitorId')
    where
      abstract
        natural : {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                → η ∘ᵥ λ' f ≡ λ' g ∘ᵥ (η ∘ₕ id₂ {a} {a})
        natural {f} {g} {η} = ≅-to-≡ $ hbegin
          η ∘ᵥ λ' f 
            ≅⟨ compᵥ-cong₂ left-id refl refl refl (het-help (λ' f) id₂ (sym left-id) refl refl) ⟩
          η ∘ᵥ id₂
            ≅⟨ ≡-to-≅ v-left-id ⟩
          η
            ≅⟨ ≡-to-≅ (sym v-right-id) ⟩
          id₂ ∘ᵥ η
            ≅⟨ compᵥ-cong₂ (sym left-id) (sym left-id) refl (het-help id₂ (λ' g) left-id refl (subst-swap left-id refl refl)) (hsym h-left-id) ⟩
          λ' g ∘ᵥ (η ∘ₕ id₂ {a} {a}) ∎h
  
  open Theory.Triple.Triple
  
  associator-iso : {a b c d : Cell₀} → NaturalIsomorphism [ biAssocFunctorL (comp {b} {c} {d}) (comp {a} {b} {d}) ]∘[ assocFunctorL ] 
                                                          [ biAssocFunctorR (comp {a} {c} {d}) (comp {a} {b} {c}) ]∘[ assocFunctorR ]
  associator-iso {a} {b} {c} {d} = naturalIsomorphism (naturalTransformation (λ x → α' (proj₃ x) (proj₂ x) (proj₁ x)) natural) (λ x → isomorphism (α (proj₃ x) (proj₂ x) (proj₁ x)) associatorId' associatorId)
    where
      _∘HC_ = Category._∘_ (HomCat a d)
      
      abstract
        natural : {f g : Obj (HomCat c d ×C HomCat b c ×C HomCat a b)} {η : Hom (HomCat c d ×C HomCat b c ×C HomCat a b) f g} 
                → (proj₁ η ∘ₕ (proj₂ η ∘ₕ proj₃ η)) ∘ᵥ α' (proj₃ f) (proj₂ f) (proj₁ f)
                ≡ α' (proj₃ g) (proj₂ g) (proj₁ g) ∘ᵥ ((proj₁ η ∘ₕ proj₂ η) ∘ₕ proj₃ η) -- [ [ biAssocFunctorL comp comp ]∘[ assocFunctorL ] ]₁ η
        natural {f ,' f' ,' f''} {g ,' g' ,' g''} {η ,' η' ,' η''} = ≅-to-≡ $ hbegin
          (η ∘ₕ (η' ∘ₕ η'')) ∘ᵥ α' f'' f' f
            ≅⟨ compᵥ-cong₂ (sym assoc) refl refl refl (het-help (α' f'' f' f) id₂ assoc refl refl) ⟩
          (η ∘ₕ (η' ∘ₕ η'')) ∘ᵥ id₂
            ≅⟨ ≡-to-≅ v-left-id ⟩
          η ∘ₕ (η' ∘ₕ η'')
            ≅⟨ ≡-to-≅ (sym v-right-id) ⟩
          id₂ ∘ᵥ (η ∘ₕ (η' ∘ₕ η''))
            ≅⟨ compᵥ-cong₂ assoc assoc refl (het-help id₂ (α' g'' g' g) (sym assoc) refl (subst-swap' assoc refl refl)) h-assoc ⟩
          α' g'' g' g ∘ᵥ ((η ∘ₕ η') ∘ₕ η'') ∎h
  
  abstract
    triangle-id : {a b c : Cell₀} (f : Cell₁ a b) (g : Cell₁ b c) 
                → λ' g ∘ₕ id₂ ≡ (id₂ ∘ₕ ρ f) ∘ᵥ α' f id₁ g
    triangle-id f g = ≅-to-≡ $ hbegin
      λ' g ∘ₕ id₂ 
        ≅⟨ compₕ-cong₂ left-id refl refl refl refl (het-help (λ' g) id₂ (sym left-id) refl refl) ⟩
      id₂ {f = g} ∘ₕ id₂ {f = f}
        ≅⟨ compₕ-cong₂ refl refl (sym right-id) (sym right-id) (id≅id (sym right-id)) refl ⟩
      id₂ {f = g} ∘ₕ id₂ {f = id₁ ∘ f}
        ≅⟨ ≡-to-≅ (sym v-left-id) ⟩
      (id₂ ∘ₕ id₂) ∘ᵥ id₂
        ≅⟨ compᵥ-cong₂ assoc refl (cong (λ X → g ∘ X) right-id) 
                       (compₕ-cong₂ refl refl refl right-id (het-help id₂ (ρ f) refl (sym right-id) (subst-swap refl (sym right-id) p)) refl) 
                       (het-help id₂ (α' f id₁ g) (sym assoc) refl (subst-swap' assoc refl refl)) ⟩
      (id₂ ∘ₕ ρ f) ∘ᵥ α' f id₁ g ∎h
      where
        abstract
          p : subst₂ Cell₂ refl (sym (sym right-id)) id₂ ≡ ρ f
          p = ≅-to-≡ $ hbegin
            subst₂ Cell₂ refl (sym (sym right-id)) id₂ 
              ≅⟨ subst-id refl (sym (sym right-id)) ⟩
            id₂ {f = f}
              ≅⟨ hsym (subst-id (sym right-id) refl) ⟩
            subst₂ Cell₂ (sym right-id) refl id₂
              ≅⟨ refl ⟩
            ρ f ∎h
  
  abstract
    pentagon-id : {a b c d e : Cell₀} 
                → (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d) (k : Cell₁ d e)
                → (id₂ {f = k} ∘ₕ α' f g h) ∘ᵥ (α' f (h ∘ g) k ∘ᵥ (α' g h k ∘ₕ id₂ {f = f}))
                ≡ α' (g ∘ f) h k ∘ᵥ α' f g (k ∘ h)
    pentagon-id f g h k = ≅-to-≡ $ hbegin
      (id₂ {f = k} ∘ₕ α' f g h) ∘ᵥ (α' f (h ∘ g) k ∘ᵥ (α' g h k ∘ₕ id₂ {f = f}))
        ≅⟨ compᵥ-cong₂ refl refl (cong (λ X → k ∘ X) assoc) (compₕ-cong₂ refl refl refl assoc (het-help (α' f g h) id₂ refl (sym assoc) (subst-swap'' assoc)) refl) refl ⟩
      (id₂ {f = k} ∘ₕ id₂ {f = (h ∘ g) ∘ f}) ∘ᵥ (α' f (h ∘ g) k ∘ᵥ (α' g h k ∘ₕ id₂ {f = f}))
        ≅⟨ compᵥ-cong₂ refl refl refl (≡-to-≅ id∘ₕid≡id) refl ⟩
      (id₂ {f = k ∘ ((h ∘ g) ∘ f)}) ∘ᵥ (α' f (h ∘ g) k ∘ᵥ (α' g h k ∘ₕ id₂ {f = f}))
        ≅⟨ ≡-to-≅ v-right-id ⟩
      α' f (h ∘ g) k ∘ᵥ (α' g h k ∘ₕ id₂ {f = f})
        ≅⟨ compᵥ-cong₂ refl refl assoc (het-help (α' f (h ∘ g) k) id₂ refl (sym assoc) (subst-swap'' assoc)) refl ⟩
      id₂ {f = (k ∘ (h ∘ g)) ∘ f} ∘ᵥ (α' g h k ∘ₕ id₂ {f = f})
        ≅⟨ ≡-to-≅ v-right-id ⟩
      α' g h k ∘ₕ id₂ {f = f}
        ≅⟨ compₕ-cong₂ refl assoc refl refl refl (het-help (α' g h k) id₂ refl (sym assoc) (subst-swap'' assoc)) ⟩
      id₂ {f = (k ∘ h) ∘ g} ∘ₕ id₂ {f = f}
        ≅⟨ ≡-to-≅ id∘ₕid≡id ⟩
      id₂ {f = ((k ∘ h) ∘ g) ∘ f}
        ≅⟨ id≅id (sym assoc) ⟩
      id₂ {f = (k ∘ h) ∘ (g ∘ f)}
        ≅⟨ ≡-to-≅ (sym v-right-id) ⟩
      id₂ {f = (k ∘ h) ∘ (g ∘ f)} ∘ᵥ id₂ {f = (k ∘ h) ∘ (g ∘ f)} 
        ≅⟨ compᵥ-cong₂ assoc refl (sym assoc) (het-help id₂ (α' (g ∘ f) h k) refl assoc 
                       (subst-swap refl assoc (sym (subst-swap'' assoc)))) 
                       (het-help id₂ (α' f g (k ∘ h)) (sym assoc) refl (subst-swap' assoc refl refl)) ⟩
      α' (g ∘ f) h k ∘ᵥ α' f g (k ∘ h) ∎h
    
  abstract
    interchange : {a b c : Cell₀} 
                → {x y z : Obj (HomCat a b)} {x' y' z' : Obj (HomCat b c)}
                → (f : Hom (HomCat a b) x y) (f' : Hom (HomCat b c) x' y') (g : Hom (HomCat a b) y z) (g' : Hom (HomCat b c) y' z')
                → (g' ∘ᵥ f') ∘ₕ (g ∘ᵥ f) ≡ (g' ∘ₕ g) ∘ᵥ (f' ∘ₕ f)
    interchange {x} {y} {z} {x'} {y'} {z'} f f' g g' = begin
      [ comp ]₁ ((g' ∘ᵥ f') , (g ∘ᵥ f)) 
        ≡⟨ Functor.compose comp ⟩
      ([ comp ]₁ (g' , g)) ∘ᵥ ([ comp ]₁ (f' , f)) ∎
  
  category : Category {ℓ₀} {ℓ₁}
  category = Category.category Cell₀ Cell₁ _∘_ id₁ assoc right-id left-id
  
  whiskerCoher1' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h i : Obj (HomCat c d)} {η : Hom (HomCat c d) h i}
                 → η ∘ₕ id₂ {a} {c}
                 ≡ subst₂ Cell₂ (sym (assoc {f = f} {g = g})) (sym assoc) (((η ∘ₕ id₂ {b} {c})) ∘ₕ id₂ {a} {b})
  whiskerCoher1' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym (assoc {f = f} {g = g})) (sym assoc) (htrans (hcong (λ X → η ∘ₕ X) (hsym (≡-to-≅ id∘ₕid≡id))) h-assoc)
  
  whiskerCoher2' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g h : Obj (HomCat b c)} {i : Obj (HomCat c d)} {η : Hom (HomCat b c) g h} 
                 → id₂ {f = i} ∘ₕ (η ∘ₕ id₂ {f = f}) 
                 ≡ subst₂ Cell₂ (sym (assoc {f = f} {g = g})) (sym (assoc {f = f} {g = h})) ((id₂ {c} {d} ∘ₕ η) ∘ₕ id₂ {a} {b})
  whiskerCoher2' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym (assoc {f = f} {g = g})) (sym (assoc {f = f} {g = h})) h-assoc
  
  whiskerCoher3' : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                 → id₂ {f = i} ∘ₕ (id₂ {f = h} ∘ₕ η) 
                 ≡ subst₂ Cell₂ (sym assoc) (sym assoc) (id₂ {f = i ∘ h} ∘ₕ η)
  whiskerCoher3' {a} {b} {c} {d} {f} {g} {h} {i} {η} = het-to-prop (sym assoc) (sym assoc) (htrans h-assoc (hcong (λ X → X ∘ₕ η) (≡-to-≅ id∘ₕid≡id)))
  
  whiskerCoher4' : {a b c : Cell₀} {f g : Cell₁ a b} {h i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ h i}
                 → (id₂ {f = i} ∘ₕ η) ∘ᵥ (θ ∘ₕ id₂ {f = f}) ≡ (θ ∘ₕ id₂ {f = g}) ∘ᵥ (id₂ {f = h} ∘ₕ η)
  whiskerCoher4' {a} {b} {c} {f} {g} {h} {i} {η} {θ} = ≅-to-≡ $ hbegin
    (id₂ {f = i} ∘ₕ η) ∘ᵥ (θ ∘ₕ id₂ {f = f}) 
      ≅⟨ ≡-to-≅ (sym $ interchange id₂ θ η id₂) ⟩
    (id₂ {f = i} ∘ᵥ θ) ∘ₕ (η ∘ᵥ id₂ {f = f}) 
      ≅⟨ hcong₂ _∘ₕ_ (≡-to-≅ v-right-id) (≡-to-≅ v-left-id) ⟩
    θ ∘ₕ η
      ≅⟨ hcong₂ _∘ₕ_ (≡-to-≅ (sym v-left-id)) (≡-to-≅ (sym v-right-id)) ⟩
    (θ ∘ᵥ id₂ {f = h}) ∘ₕ (id₂ {f = g} ∘ᵥ η)
      ≅⟨ ≡-to-≅ (interchange η id₂ id₂ θ) ⟩
    (θ ∘ₕ id₂ {f = g}) ∘ᵥ (id₂ {f = h} ∘ₕ η) ∎h
  
  abstract
    whiskerRightDist : {a b c : Cell₀} {f : Cell₁ a b} {g h i : Cell₁ b c} {η : Cell₂ g h} {θ : Cell₂ h i}
                     → (θ ◁ f) ∘ᵥ (η ◁ f) ≡ (θ ∘ᵥ η) ◁ f
    whiskerRightDist {a} {b} {c} {f} {η = η} {θ} = 
      let _∘bc_ = Category._∘_ (HomCat b c)
      in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (θ ∘bc η , X)) v-left-id)
  
  abstract
    whiskerLeftDist : {a b c : Cell₀} {f g h : Cell₁ a b} {i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ g h}
                    → (i ▷ θ) ∘ᵥ (i ▷ η) ≡ i ▷ (θ ∘ᵥ η)
    whiskerLeftDist {a} {b} {c} {η = η} {θ} = 
      let _∘ab_ = Category._∘_ (HomCat a b)
      in trans (sym (Functor.compose comp)) (cong (λ X → [ comp ]₁ (X , θ ∘ab η)) v-left-id)
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher1 : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                → η ◁ (g ∘ f) ≡ subst₂ Cell₂ (sym assoc) (sym assoc) ((η ◁ g) ◁ f)
  whiskerCoher1 = whiskerCoher1'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher2 : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                → i ▷ (η ◁ f) ≡ subst₂ Cell₂ (sym assoc) (sym assoc) ((i ▷ η) ◁ f)
  whiskerCoher2 = whiskerCoher2'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher3 : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                → i ▷ (h ▷ η) ≡ subst₂ Cell₂ (sym assoc) (sym assoc) ((i ∘ h) ▷ η)
  whiskerCoher3 = whiskerCoher3'

  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerCoher4 : {a b c : Cell₀} {f g : Cell₁ a b} {h i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ h i}
                → (i ▷ η) ∘ᵥ (θ ◁ f) ≡ (θ ◁ g) ∘ᵥ (h ▷ η)
  whiskerCoher4 = whiskerCoher4'
  
  abstract
    whiskerCoher1-het : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h i : Cell₁ c d} {η : Cell₂ h i}
                      → η ◁ (g ∘ f) ≅ (η ◁ g) ◁ f
    whiskerCoher1-het {f = f} {g} {η = η} = het-help (η ◁ (g ∘ f)) ((η ◁ g) ◁ f) (sym assoc) (sym assoc) whiskerCoher1
  
  abstract
    whiskerCoher2-het : {a b c d : Cell₀} {f : Cell₁ a b} {g h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ g h} 
                      → i ▷ (η ◁ f) ≅ (i ▷ η) ◁ f
    whiskerCoher2-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (η ◁ f)) ((i ▷ η) ◁ f) (sym assoc) (sym assoc) whiskerCoher2
  
  abstract
    whiskerCoher3-het : {a b c d : Cell₀} {f g : Cell₁ a b} {h : Cell₁ b c} {i : Cell₁ c d} {η : Cell₂ f g}
                      → i ▷ (h ▷ η) ≅ (i ∘ h) ▷ η
    whiskerCoher3-het {f = f} {g} {h} {i} {η} = het-help (i ▷ (h ▷ η)) ((i ∘ h) ▷ η) (sym assoc) (sym assoc) whiskerCoher3

  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} 
                 → id₂ {f = g} ◁ f ≡ id₂ {f = g ∘ f}
  whiskerLeftId₁ = Functor.id comp
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₁ : {a b c : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c}
                  → g ▷ id₂ {f = f} ≡ id₂ {f = g ∘ f}
  whiskerRightId₁ = Functor.id comp
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≡ subst₂ Cell₂ (sym left-id) (sym left-id) η
  whiskerRightId₂' = h-left-id'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerRightId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≅ η
  whiskerRightId₂ {a} {b} {η = η} = het-help (η ◁ id₁ {a}) (η) (sym left-id) (sym left-id) whiskerRightId₂'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₂' : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≡ subst₂ Cell₂ (sym right-id) (sym right-id) η
  whiskerLeftId₂' = horizontal-right-id'
  
  -- This is a synonym, it should be exchangeable with its definition. Don't make it abstract!
  whiskerLeftId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≅ η
  whiskerLeftId₂ {a} {b} {η = η} = het-help (id₁ {b} ▷ η) (η) (sym right-id) (sym right-id) whiskerLeftId₂'  

  -- END StrictTwoCategory

StrictTwoCategory→Category : ∀ {ℓ₀ ℓ₁ ℓ₂} → StrictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} → Category {ℓ₀} {ℓ₁}
StrictTwoCategory→Category = StrictTwoCategory.category

