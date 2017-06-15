
open import Level

open import Data.Product using ( _,_ )

open import Relation.Binary.PropositionalEquality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Application
open Theory.Functor.Application.BiFunctor
open import Theory.Functor.Association
open Theory.Functor.Association.Triple
open Theory.Functor.Association.BiFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

-- | Definition of bicategories as given in the nCatLab wiki:
--   https://ncatlab.org/nlab/show/bicategory
module Theory.TwoCategory.Bicategory where

open Category

record Bicategory {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Cell₀ : Set ℓ₀
    HomCat : Cell₀ → Cell₀ → Category {ℓ₁} {ℓ₂}
  
  Cell₁ : Cell₀ → Cell₀ → Set ℓ₁
  Cell₁ a b = Category.Obj (HomCat a b)
  
  Cell₂ : {a b : Cell₀} → Cell₁ a b → Cell₁ a b → Set ℓ₂
  Cell₂ {a} {b} f g = Category.Hom (HomCat a b) f g
   
  field
    -- Identity 1-cell
    id₁ : (a : Cell₀) → Cell₁ a a
    
    -- Horizontal composition
    compₕ : {a b c : Cell₀} → Functor ((HomCat b c) ×C (HomCat a b)) (HomCat a c)
  
  _∘ᵥ_ : {a b : Cell₀} {f g h : Obj (HomCat a b)} → Hom (HomCat a b) g h → Hom (HomCat a b) f g → Hom (HomCat a b) f h
  _∘ᵥ_ {a} {b} {f} {g} {h} = _∘_ (HomCat a b)
  
  id₂ : {a b : Cell₀} → (f : Cell₁ a b) → Cell₂ f f
  id₂ {a} {b} f = Category.id (HomCat a b) {f}
  
  I : (a : Cell₀) → Functor ⊤-Cat (HomCat a a)
  I a = functor (λ _ → id₁ a) (λ _ → id₂ (id₁ a)) refl (sym (Category.left-id (HomCat a a)))
  
  field
    -- Left unitor
    left-unitor : {a b : Cell₀} → NaturalIsomorphism ([ id₁ b ,-] compₕ {a} {b} {b}) Id[ HomCat a b ]

    -- Right unitor
    right-unitor : {a b : Cell₀} → NaturalIsomorphism ([-, id₁ a ] compₕ {a} {a} {b}) Id[ HomCat a b ]
    
    -- Associator
    associator : {a b c d : Cell₀} → NaturalIsomorphism [ biAssocFunctorL (compₕ {b} {c} {d}) (compₕ {a} {b} {d}) ]∘[ assocFunctorL ] 
                                                        [ biAssocFunctorR (compₕ {a} {c} {d}) (compₕ {a} {b} {c}) ]∘[ assocFunctorR ]
  
  _∘₁_ : {a b c : Cell₀} → Obj (HomCat b c) → Obj (HomCat a b) → Obj (HomCat a c)
  _∘₁_ {a} {b} {c} f g = Functor.F₀ (compₕ {a} {b} {c}) (f , g)
  
  α : {a b c d : Cell₀} (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d) → Hom (HomCat a d) ((h ∘₁ g) ∘₁ f) (h ∘₁ (g ∘₁ f))
  α h g f = NaturalIsomorphism.η associator (f ,' g ,' h)
  
  r : {a b : Cell₀} (f : Cell₁ a b) → Hom (HomCat a b) (f ∘₁ id₁ a) f
  r f = NaturalIsomorphism.η right-unitor f

  l : {a b : Cell₀} (f : Cell₁ a b) → Hom (HomCat a b) (id₁ b ∘₁ f) f
  l f = NaturalIsomorphism.η left-unitor f
  
  α' : {a b c d : Cell₀} (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d) → Hom (HomCat a d) (h ∘₁ (g ∘₁ f)) ((h ∘₁ g) ∘₁ f)
  α' h g f = NaturalIsomorphism.inv associator (f ,' g ,' h)
  
  r' : {a b : Cell₀} (f : Cell₁ a b) → Hom (HomCat a b) f (f ∘₁ id₁ a)
  r' f = NaturalIsomorphism.inv right-unitor f

  l' : {a b : Cell₀} (f : Cell₁ a b) → Hom (HomCat a b) f (id₁ b ∘₁ f)
  l' f = NaturalIsomorphism.inv left-unitor f
  
  _∘ₕ_ : {a b c : Cell₀} {f f' : Obj (HomCat b c)} {g g' : Obj (HomCat a b)}
       → Hom (HomCat b c) f f' → Hom (HomCat a b) g g' → Hom (HomCat a c) (f ∘₁ g) (f' ∘₁ g')
  _∘ₕ_ {a} {b} {c} {f} {f'} {g} {g'} α β = Functor.F₁ (compₕ {a} {b} {c}) {f , g} {f' , g'} (α , β)
  
  field
    triangle-id : {a b c : Cell₀} → (f : Cell₁ a b) → (g : Cell₁ b c) → r g ∘ₕ id₂ f ≡ (id₂ g ∘ₕ l f) ∘ᵥ α f (id₁ b) g

    pentagon-id : {a b c d e : Cell₀} (f : Cell₁ a b) (g : Cell₁ b c) (h : Cell₁ c d) (k : Cell₁ d e)
                → (id₂ k ∘ₕ α f g h) ∘ᵥ (α f (h ∘₁ g) k ∘ᵥ (α g h k ∘ₕ id₂ f)) ≡ α (g ∘₁ f) h k ∘ᵥ α f g (k ∘₁ h)
  
