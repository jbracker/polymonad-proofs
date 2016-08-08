
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
    Cell₀ : Set ℓ₀
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}

    --                       (b c × a b ↦ a c)
    comp : {a b c : Cell₀} → Functor (HomCat b c ×C HomCat a b) (HomCat a c) 
    id₁  : {a : Cell₀} → Obj (HomCat a a)
    
    horizontalIdR₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
                   → [ comp {a} {a} {b} ]₀ (f , id₁ {a}) ≡ f
    
    horizontalIdR₂ : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                   → [ comp {a} {a} {b} ]₁ (η , idC (HomCat a a)) ≡ subst₂ (Hom (HomCat a b)) (sym horizontalIdR₁) (sym horizontalIdR₁) η
    
    horizontalIdL₁ : {a b : Cell₀} {f : Obj (HomCat a b)} 
                   → [ comp {a} {b} {b} ]₀ (id₁ {b} , f) ≡ f
    
    horizontalIdL₂ : {a b : Cell₀} {f g : Obj (HomCat a b)} {η : Hom (HomCat a b) f g} 
                   → [ comp {a} {b} {b} ]₁ (idC (HomCat b b), η) ≡ subst₂ (Hom (HomCat a b)) (sym horizontalIdL₁) (sym horizontalIdL₁) η

    horizontalAssoc₁ : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h : Obj (HomCat c d)}
                     → [ comp ]₀ (h , [ comp ]₀ (g , f)) ≡ [ comp ]₀ ([ comp ]₀ (h , g) , f)
    
    horizontalAssoc₂ : {a b c d : Cell₀} {f f' : Obj (HomCat a b)} {g g' : Obj (HomCat b c)} {h h' : Obj (HomCat c d)}
                     → {η : Hom (HomCat c d) h h'} {θ : Hom (HomCat b c) g g'} {ι : Hom (HomCat a b) f f'}
                     → ([ comp ]₁ (η , [ comp ]₁ (θ , ι))) ≡ subst₂ (Hom (HomCat a d)) (sym horizontalAssoc₁) (sym horizontalAssoc₁) ([ comp ]₁ ([ comp ]₁ (η , θ) , ι))
    
    whiskerCoher1' : {a b c d : Cell₀} {f : Obj (HomCat a b)} {g : Obj (HomCat b c)} {h i : Obj (HomCat c d)} {η : Hom (HomCat c d) h i}
                   → [ comp ]₁ (η , idC (HomCat a c)) ≡ subst₂ (Hom (HomCat a d)) (sym (horizontalAssoc₁ {f = f} {g = g})) (sym horizontalAssoc₁) ([ comp ]₁ ([ comp ]₁ (η , idC (HomCat b c)) , idC (HomCat a b)))
    
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

  vIdR : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → θ ∘ᵥ id₂ ≡ θ
  vIdR {a} {b} = Category.idR (HomCat a b)

  vIdL : {a b : Cell₀} {f g : Cell₁ a b} {θ : Cell₂ f g} → id₂ ∘ᵥ θ ≡ θ
  vIdL {a} {b} = Category.idL (HomCat a b)
  
  vAssoc : {a b : Cell₀} {f g h i : Cell₁ a b} {η : Cell₂ f g} {θ : Cell₂ g h} {ι : Cell₂ h i}
                → ι ∘ᵥ (θ ∘ᵥ η) ≡ (ι ∘ᵥ θ) ∘ᵥ η
  vAssoc {a} {b} = Category.assoc (HomCat a b)
  
  hIdR₁ : {a b : Cell₀} {f : Cell₁ a b} → f ∘ₕ id₁ {a} ≡ f
  hIdR₁ = horizontalIdR₁
  
  hIdL₁ :  {a b : Cell₀} {f : Cell₁ a b} → id₁ {b} ∘ₕ f ≡ f
  hIdL₁ = horizontalIdL₁

  hIdR₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
        → η ∘ₕ₂ id₂ {a} {a} ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  hIdR₂ = horizontalIdR₂

  hIdL₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} 
        → id₂ {b} {b} ∘ₕ₂ η ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  hIdL₂ = horizontalIdL₂
  
  hAssoc₁ : {a b c d : Cell₀} {f : Cell₁ a b} {g : Cell₁ b c} {h : Cell₁ c d} → h ∘ₕ (g ∘ₕ f) ≡ (h ∘ₕ g) ∘ₕ f
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
  
  whiskerLeftId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → η ◁ id₁ {a} ≡ subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
  whiskerLeftId₂ = horizontalIdR₂
  
  whiskerRightId₂ : {a b : Cell₀} {f g : Cell₁ a b} {η : Cell₂ f g} → id₁ {b} ▷ η ≡ subst₂ Cell₂ (sym hIdL₁) (sym hIdL₁) η
  whiskerRightId₂ = horizontalIdL₂

  whiskerLeftDist : {a b c : Cell₀} {f : Cell₁ a b} {g h i : Cell₁ b c} {η : Cell₂ g h} {θ : Cell₂ h i}
                  → (θ ◁ f) ∘ᵥ (η ◁ f) ≡ (θ ∘ᵥ η) ◁ f
  whiskerLeftDist {a} {b} {c} {f} {η = η} {θ} = 
    let id' : Cell₂ f f
        id' = Category.id (HomCat a b)
        _∘ab_ = Category._∘_ (HomCat a b)
        _∘ac_ = Category._∘_ (HomCat a c)
        _∘bc_ = Category._∘_ (HomCat b c)
    in begin
    (θ ◁ f) ∘ᵥ (η ◁ f) 
      ≡⟨ refl ⟩
    ([ comp ]₁ (θ , id')) ∘ac ([ comp ]₁ (η , id'))
      ≡⟨ sym (Functor.dist comp) ⟩
    [ comp ]₁ (θ ∘bc η , id' ∘ab id')
      ≡⟨ cong (λ X → [ comp ]₁ (θ ∘bc η , X)) vIdL ⟩
    [ comp ]₁ (θ ∘bc η , id')
      ≡⟨ refl ⟩
    (θ ∘ᵥ η) ◁ f ∎

  whiskerRightDist : {a b c : Cell₀} {f g h : Cell₁ a b} {i : Cell₁ b c} {η : Cell₂ f g} {θ : Cell₂ g h}
                   → (i ▷ θ) ∘ᵥ (i ▷ η) ≡ i ▷ (θ ∘ᵥ η)
  whiskerRightDist {a} {b} {c} {η = η} {θ} = 
    let _∘ab_ = Category._∘_ (HomCat a b)
    -- Similar as in 'whiskerLeftDist'
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
  {-
  
  idLeftFunctorEq : {a b : Cell₀} 
                  -- (a b × a a ↦ a b)  ∘  (a b ↦ a b × a a)
                  → [ comp {a} {a} {b} ]∘[ [ Id[ HomCat a b ] ]◁[ HomCat a a , id₁ {a} ] ]
                  -- (a b ↦ a b) 
                  ≡ Id[ HomCat a b ]
  idLeftFunctorEq {a} {b} = propEqFunctor p1 p2
    where
      p1 : Functor.F₀ [ comp {a} {a} {b} ]∘[ [ Id[ HomCat a b ] ]◁[ HomCat a a , id₁ {a} ] ] ≡ λ x → x
      p1 = funExt $ λ f → hIdR₁ {f = f}
 
      p3 : {f g : Cell₁ a b} {η : Cell₂ f g}
         → subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
         ≡ subst₂ (λ X Y → (f' g' : Cell₁ a b) → Cell₂ f' g' → Cell₂ (X f') (Y g')) (sym (funExt $ λ f → hIdR₁ {f = f})) (sym (funExt $ λ f → hIdR₁ {f = f})) (λ f' g' η' → η') f g η ∎
      p3 = ?

      p2 : (λ f g → Functor.F₁ ([ comp {a} {a} {b} ]∘[ [ Id[ HomCat a b ] ]◁[ HomCat a a , id₁ {a} ] ]) {f} {g})
         ≡ subst₂ (λ X Y → (f g : Cell₁ a b) → Cell₂ f g → Cell₂ (X f) (Y g)) (sym p1) (sym p1) (λ f g η → η)
      p2 = funExt $ λ f → funExt $ λ g → funExt $ λ η → begin
        Functor.F₁ [ comp ]∘[ [ Id[ HomCat a b ] ]◁[ HomCat a a , id₁ ] ] η
          ≡⟨ refl ⟩
        [ comp ]₁ (η , id₂)
          ≡⟨ refl ⟩
        η ◁ id₁
          ≡⟨ whiskerLeftId₂ ⟩
        subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
          ≡⟨ refl ⟩
        subst₂ Cell₂ (sym hIdR₁) (sym hIdR₁) η
          ≡⟨ {!!} ⟩
        subst₂ (λ X Y → (f' g' : Cell₁ a b) → Cell₂ f' g' → Cell₂ (X f') (Y g')) (sym p1) (sym p1) (λ f' g' η' → η') f g η ∎
  -}
