
module Theory.Examples.HaskellFunctorToFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )

-- Local
open import Haskell
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Category
open import Theory.Functor
open import Theory.Examples.Category

open Category

HaskellFunctor→Functor : {F : Type → Type}
                       → HaskellFunctor F → Functor (setCategory {lzero}) (setCategory {lzero})
HaskellFunctor→Functor {F} func = functor F₀ F₁ (HaskellFunctor.lawId func) (λ {a} {b} {c} {f} {g} → HaskellFunctor.lawDist func g f) 
  where
    C = setCategory {lzero}
    
    F₀ : Obj C → Obj C
    F₀ α = F α
    
    F₁ : {a b : Obj C} → Hom C a b → Hom C (F₀ a) (F₀ b)
    F₁ f = HaskellFunctor.fmap func f
