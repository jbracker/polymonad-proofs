 
module Supermonad.DefinitionWithCategory.ToLaxTwoFunctor where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec hiding ( _>>=_ )
open import Data.List hiding ( sequence )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Utilities
open import Haskell
open import Haskell.Constrained.ConstrainedFunctor
open import Supermonad.DefinitionWithCategory
open import Theory.Category
open import Theory.Examples.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Monad
open import Theory.TwoCategory
open import Theory.Examples.TwoCategory
open import Theory.TwoFunctor 

open StrictTwoCategory

open Category

SupermonadC→LaxTwoFunctor 
  : ∀ {ℓ₀ ℓ₁} 
  → {C : Category {ℓ₀} {ℓ₁}} 
  → {M : ∀ {a b} → Hom C a b → TyCon} 
  → SupermonadC {ℓF = ℓ₀ ⊔ ℓ₁} C M → LaxTwoFunctor (Category→StrictTwoCategory C) (functorTwoCategory {lsuc lzero} {lzero})
SupermonadC→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {M} smc = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = {!!}
  ; μ = {!!}
  ; laxFunId₁ = {!!}
  ; laxFunId₂ = {!!}
  ; laxFunAssoc = {!!}
  }
  where
    fmap : {a b : Obj C} (f : Hom C a b) → {α β : Type} → ConstrainedFunctor.FunctorCts (SupermonadC.functor smc f) α β → (α → β) → M f α → M f β
    fmap f = ConstrainedFunctor.fmap (SupermonadC.functor smc f)
    
    P₀ : Obj C → Category {lsuc lzero} {lzero}
    P₀ _ = setCategory
    
    P₁ : {x y : Obj C} → Functor (HomCat (Category→StrictTwoCategory C) x y) (HomCat functorTwoCategory (P₀ x) (P₀ y))
    P₁ {x} {y} = functor F₀ (λ {a} {b} → F₁ {a} {b}) {!!} {!!}
      where 
        F₀ : Hom C x y → Functor (P₀ x) (P₀ y)
        F₀ f = functor F₀' F₁' {!!} {!!}
          where
            F₀' : Obj (P₀ x) → Obj (P₀ y)
            F₀' = M f

            F₁' : {a b : Obj (P₀ x)} → Hom (P₀ x) a b → Hom (P₀ y) (F₀' a) (F₀' b)
            F₁' = fmap f {!!}
    
        F₁ : {a b : Hom C x y} 
           → Hom (HomCat (Category→StrictTwoCategory C) x y) a b
           → Hom (HomCat functorTwoCategory (P₀ x) (P₀ y)) (F₀ a) (F₀ b)
        F₁ tt = {!!}
