
module Theory.TwoFunctor.Properties.FromFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- Local
open import Theory.Category.Definition
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
  ; η = lift tt
  ; μ = lift tt
  ; laxFunId₁ = refl
  ; laxFunId₂ = refl
  ; laxFunAssoc = refl
  ; μ-natural₁ = λ f → refl
  ; μ-natural₂ = λ g → refl
  } where
      open StrictTwoCategory
      open Category
      
      C' = codiscreteHomCatTwoCategory C
      D' = codiscreteHomCatTwoCategory D
      
      P₀ : Cell₀ C' → Cell₀ D'
      P₀ a = [ F ]₀ a
      
      P₁ : {x y : Cell₀ C'} → Functor (HomCat C' x y) (HomCat D' (P₀ x) (P₀ y))
      P₁ {x} {y} = record 
        { F₀ = F₀
        ; F₁ = λ {a} {b} → F₁ {a} {b}
        ; id = refl
        ; compose = refl
        } where
          F₀ : Obj (HomCat C' x y) → Obj (HomCat D' (P₀ x) (P₀ y))
          F₀ f = [ F ]₁ f
          
          F₁ : {a b : Obj (HomCat C' x y)} 
             → Hom (HomCat C' x y) a b → Hom (HomCat D' (P₀ x) (P₀ y)) (F₀ a) (F₀ b)
          F₁ f = lift tt
 
