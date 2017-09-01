
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ )

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.Definition


open Category hiding ( _∘_ )
open StrictTwoCategory

module Theory.TwoFunctor.ConstZeroCell where

record ConstLaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                          (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                          (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                          (constD : Cell₀ D) 
                     : Set (suc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  constructor const-lax-two-functor

  private
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C

    _∘Dₕ_ = _∘ₕ_ D
    _∘Cₕ_ = _∘ₕ_ C

    _∘Dᵥ_ = _∘ᵥ_ D
    _∘Cᵥ_ = _∘ᵥ_ C

    id₁D = id₁ D

    P₀ : Cell₀ C → Cell₀ D
    P₀ _ = constD

  field
    -- P_{x,y}
    P₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀ x) (P₀ y))
    
    -- P_{id_x}
    η : {x : Cell₀ C}
      → Cell₂ D (id₁ D {P₀ x}) ([ P₁ {x} {x} ]₀ (id₁ C {x}))

    -- P_{x,y,z}
    μ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z}
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → Cell₂ D ([ P₁ ]₀ g  ∘D  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘C f))
    
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → μ {x} {x} {y} {id₁ C {x}} {f} ∘Dᵥ (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ η {x})
              ≅ id₂ D {f = [ P₁ {x} {y} ]₀ f}
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → μ {x} {y} {y} {f} {id₁ C {y}} ∘Dᵥ (η {y} ∘Dₕ id₂ D {f = [ P₁ {x} {y} ]₀ f}) 
              ≅ id₂ D {f = [ P₁ {x} {y} ]₀ f}

    -- μ ∘ᵥ (id₂ ∘ₕ μ) ≅ μ ∘ᵥ (μ ∘ₕ id₂)
    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
                → μ {w} {y} {z} {g ∘C f} {h} ∘Dᵥ (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ μ {w} {x} {y} {f} {g})
                ≅ μ {w} {x} {z} {f} {h ∘C g} ∘Dᵥ (μ {x} {y} {z} {g} {h} ∘Dₕ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f})
    
    μ-natural₁ : {a b c : Cell₀ C} → (f : Cell₁ C a b) → {x y : Cell₁ C b c} {α : Cell₂ C x y} 
               → [ P₁ ]₁ (α ∘Cₕ id₂ C {a}) ∘Dᵥ μ {f = f} {x} ≡ μ {f = f} {y} ∘Dᵥ ([ P₁ ]₁ α ∘Dₕ [ P₁ ]₁ (id₂ C {a}))
    
    μ-natural₂ : {a b c : Cell₀ C} → (g : Cell₁ C b c) {x y : Cell₁ C a b} {α : Cell₂ C x y}
               → [ P₁ ]₁ (id₂ C {b} ∘Cₕ α) ∘Dᵥ μ {f = x} {g} ≡ μ {f = y} {g} ∘Dᵥ ([ P₁ ]₁ (id₂ C {b}) ∘Dₕ [ P₁ ]₁ α)
    
  laxTwoFunctor : LaxTwoFunctor C D
  laxTwoFunctor = record
    { P₀ = P₀
    ; P₁ = P₁
    ; η = λ {x} → η {x}
    ; μ = μ
    ; laxFunId₁ = laxFunId₁
    ; laxFunId₂ = laxFunId₂
    ; laxFunAssoc = laxFunAssoc
    ; μ-natural₁ = μ-natural₁
    ; μ-natural₂ = μ-natural₂
    }
