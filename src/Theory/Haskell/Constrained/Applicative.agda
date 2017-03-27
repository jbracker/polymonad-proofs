
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Dependent
open import Theory.Category.Examples

open import Theory.Functor
open import Theory.Functor.Monoidal

open import Theory.Natural.Transformation

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Applicative {ℓ : Level} where

private
  Hask = setCategory {ℓ}
  HaskMon = setMonoidalCategory {ℓ}
  Type = Set ℓ
  _∘Hask_ = Category._∘_ Hask

open import Theory.Functor.Composition
record ConstrainedApplicative {ℓCt₀ ℓCt₁ : Level} : Set (suc (ℓ ⊔ ℓCt₀ ⊔ ℓCt₁)) where
  open Category
  open MonoidalCategory using ( tensor ; unit )
  open Functor hiding ( F₀ )
  open ConstrainedFunctor hiding ( Cts ; CtFunctor ; map )
  
  field
    Cts : MonoidalConstraintCategory {ℓ} {ℓCt₀} {ℓCt₁}
    
    CtsFunctor : ConstrainedFunctor (DependentMonoidalCategory.DC Cts)
  
  CtCategory : Category
  CtCategory = DependentMonoidalCategory.DepCat Cts
  
  CtMonoidalCategory : MonoidalCategory CtCategory 
  CtMonoidalCategory = DependentMonoidalCategory.DepMonCat Cts
  
  CtFunctor : Functor CtCategory Hask
  CtFunctor = ConstrainedFunctor.CtFunctor CtsFunctor
  
  F₀ = Functor.F₀ CtFunctor
  _⊗₀_ = MonoidalCategory._⊗₀_ CtMonoidalCategory
  
  field
    unit-map : unit HaskMon → F₀ (unit CtMonoidalCategory)
    
    prod-map : (x y : Obj CtCategory) → (F₀ x) × (F₀ y) → F₀ (x ⊗₀ y)
    
  map = ConstrainedFunctor.map CtsFunctor

  CtApplicative : LaxMonoidalFunctor CtMonoidalCategory HaskMon
  CtApplicative = record 
    { F = CtFunctor
    ; ε = unit-map
    ; μ-natural-transformation = record
      { η = λ x → prod-map (proj₁ x) (proj₂ x)
      ; natural = {!!}
      }
    ; assoc = {!!}
    ; left-unitality = {!!}
    ; right-unitality = {!!}
    }
  {-
  pure : (A : Obj CtCategory) → (proj₁ A  → F₀ A)
  pure (A , CtA) a = map ((λ _ → a) , {!!}) (unit-map (lift tt))
  -}
