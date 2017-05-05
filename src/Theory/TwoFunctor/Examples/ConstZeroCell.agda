
open import Level

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Functor
open import Theory.TwoCategory
open import Theory.TwoFunctor


open Category
open StrictTwoCategory

module Theory.TwoFunctor.Examples.ConstZeroCell where

record ConstLaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                          (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                          (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                          (constD : Cell₀ D) 
                     : Set (suc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  private
    _∘Dₕ_ = _∘ₕ_ D
    _∘Cₕ_ = _∘ₕ_ C

    _∘Dₕ₂_ = _∘ₕ₂_ D

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
         → Cell₂ D ([ P₁ ]₀ g  ∘Dₕ  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘Cₕ f))
    
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
               → ([ P₁ {w} {z} ]₁ (α C f g h)) 
             ∘Dᵥ ( (μ {w} {y} {z} {g ∘Cₕ f} {h}) 
             ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ₂ μ {w} {x} {y} {f} {g}) ) 
               ≡ μ {w} {x} {z} {f} {h ∘Cₕ g} 
             ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ₂ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
             ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
    
  laxTwoFunctor : LaxTwoFunctor C D
  laxTwoFunctor = record
    { P₀ = P₀
    ; P₁ = P₁
    ; η = λ {x} → η {x}
    ; μ = μ
    ; laxFunId₁ = laxFunId₁
    ; laxFunId₂ = laxFunId₂
    ; laxFunAssoc = laxFunAssoc
    }
 
