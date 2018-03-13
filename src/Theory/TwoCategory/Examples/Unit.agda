
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

-- Local
open import Theory.Category.Definition hiding ( category )
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition

module Theory.TwoCategory.Examples.Unit where

open Category

-------------------------------------------------------------------------------
-- Unit strict 2-category
-------------------------------------------------------------------------------

unitStrictTwoCategory : StrictTwoCategory
unitStrictTwoCategory = record
  { Cell₀ = ⊤
  ; HomCat = HomCat
  ; comp = comp
  ; id₁ = id₁
  ; right-id = refl
  ; horizontal-right-id = refl
  ; left-id = refl
  ; horizontal-left-id = refl
  ; assoc = refl
  ; horizontal-assoc = refl
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
