
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Category.Closed
open import Theory.Category.Closed.Examples
open import Theory.Category.Closed.Dependent
open import Theory.Category.Dependent
open import Theory.Category.Examples

open import Theory.Functor
open import Theory.Functor.Closed

open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Applicative where

private
  Hask : {ℓ : Level} → ClosedCategory (setCategory {ℓ})
  Hask {ℓ} = setClosedCategory {ℓ}

record ConstrainedApplicative {ℓ ℓCt₀ ℓCt₁ : Level} : Set (suc (ℓ ⊔ ℓCt₀ ⊔ ℓCt₁)) where
  open Category
  open ClosedCategory hiding ( Obj ; Hom ; id ; _∘_ )
  open Functor hiding ( F₀ )
  open ConstrainedFunctor hiding ( Cts ; CtFunctor ; map )
  
  field
    Cts : DependentClosedCategory {ℓDep₀ = ℓ} {ℓ} (Hask {ℓ})
    
    CtsFunctor : ConstrainedFunctor (DependentClosedCategory.DC Cts)
  
  private
    _∘Hask_ = _∘_ (setCategory {ℓ})
    Type = Set ℓ
  
  open ≡-Reasoning
  
  CtCategory : Category
  CtCategory = DependentClosedCategory.DepCat Cts
  
  CtClosedCategory : ClosedCategory CtCategory 
  CtClosedCategory = DependentClosedCategory.DepClosedCat Cts

  Ct[_,_]₀ = [_,_]₀ CtClosedCategory
  
  CtFunctor : Functor CtCategory (setCategory {ℓ})
  CtFunctor = ConstrainedFunctor.CtFunctor CtsFunctor
  
  F₀ = Functor.F₀ CtFunctor
  
  field
    ap : {α β : Obj CtCategory}
       → F₀ Ct[ α , β ]₀ → (F₀ α → F₀ β)
    
    unit : F₀ (I CtClosedCategory)
  
  map = ConstrainedFunctor.map CtsFunctor

{- TODO:
  CtApplicative : LaxClosedFunctor CtClosedCategory (Hask {ℓ})
  CtApplicative = record 
    { F = CtFunctor
    ; F̂ = λ α β → ap {α} {β}
    ; F⁰ = λ _ → unit
    ; F̂-natural-x = {!!}
    ; F̂-natural-y = {!!}
    ; coher-1 = {!!}
    ; coher-2 = {!!}
    ; coher-3 = {!!}
    }
  
  open import Theory.Yoneda.Bijection
  open import Theory.Natural.Transformation
  
  pure : {α : Obj CtCategory} → proj₁ α → F₀ α
  pure {α} a = map f unit
    where 
      x = ClosedCategory.i CtClosedCategory α
      
      f : ClosedCategory.Hom CtClosedCategory (I CtClosedCategory) α
      f = proj₁ x a , {!proj₂ x!}

-}
