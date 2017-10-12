
module Theory.TwoFunctor.Properties.FromFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ; _∘_ )

open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong ; cong₂ to hcong₂ )

-- Local
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoFunctor.Definition

-------------------------------------------------------------------------------
-- Creating a Lax 2-Functor from a Functor.
-------------------------------------------------------------------------------

Functor→LaxTwoFunctor : ∀ {ℓ₀ ℓ₁} {C D : Category {ℓ₀} {ℓ₁}} 
                      → Functor C D → LaxTwoFunctor (codiscreteHomCatTwoCategory C) (codiscreteHomCatTwoCategory D)
Functor→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {D} F = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = λ {x} → codisc (id D {Functor.F₀ F x}) (Functor.F₁ F (id C))
  ; μ = λ {x y z} {f} {g} → codisc (Category._∘_ D (Functor.F₁ F g) (Functor.F₁ F f)) (Functor.F₁ F (Category._∘_ C g f)) 
  ; laxFunId₁ = λ {x y} {f} → hcong₂ codisc (≡-to-≅ $ left-id D) (≡-to-≅ $ cong (λ X → [ P₁ ]₀ X) (left-id C))
  ; laxFunId₂ = λ {x y} {f} → hcong₂ codisc (≡-to-≅ $ right-id D) (≡-to-≅ $ cong (λ X → [ P₁ ]₀ X) (right-id C))
  ; laxFunAssoc = λ {w} {x} {y} {z} {f} {g} {h} → hcong₂ codisc (≡-to-≅ $ assoc D) (≡-to-≅ (cong (λ X → [ F ]₁ X) (assoc C)))
  ; μ-natural₁ = λ { f {x} {y} {codisc .x .y} → refl }
  ; μ-natural₂ = λ { g {x} {y} {codisc .x .y} → refl }
  } where
      open StrictTwoCategory
      open Category
      
      C' = codiscreteHomCatTwoCategory C
      D' = codiscreteHomCatTwoCategory D
      
      _∘C_ = Category._∘_ C
      _∘D_ = Category._∘_ D
      
      _∘Dᵥ_ = _∘ᵥ_ D'
      _∘Dₕ_ = _∘ₕ_ D'
      
      P₀ : Cell₀ C' → Cell₀ D'
      P₀ a = [ F ]₀ a
      
      P₁ : {x y : Cell₀ C'} → Functor (HomCat C' x y) (HomCat D' (P₀ x) (P₀ y))
      P₁ {x} {y} = record 
        { F₀ = F₀
        ; F₁ = λ {a} {b} → F₁ {a} {b}
        ; id = F-id
        ; compose = F-compose
        } where
          F₀ : Obj (HomCat C' x y) → Obj (HomCat D' (P₀ x) (P₀ y))
          F₀ f = [ F ]₁ f
          
          F₁ : {a b : Obj (HomCat C' x y)} 
             → Hom (HomCat C' x y) a b → Hom (HomCat D' (P₀ x) (P₀ y)) (F₀ a) (F₀ b)
          F₁ {.a} {.b} (codisc a b) = codisc (Functor.F₁ F a) (Functor.F₁ F b)
 
          F-id : {a : Obj (HomCat C' x y)} → codisc (Functor.F₁ F a) (Functor.F₁ F a) ≡ id (HomCat D' (P₀ x) (P₀ y))
          F-id {a} = refl
          
          F-compose : {a b c : Obj (HomCat C' x y)} {f : Hom (HomCat C' x y) a b} {g : Hom (HomCat C' x y) b c}
                    → F₁ ((HomCat C' x y Category.∘ g) f) ≡ (HomCat D' (P₀ x) (P₀ y) Category.∘ F₁ g) (F₁ f)
          F-compose {a} {b} {c} {codisc .a .b} {codisc .b .c} = refl
      
