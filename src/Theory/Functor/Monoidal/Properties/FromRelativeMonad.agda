
open import Level

open import Data.Unit
open import Data.Product

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Relative

open import Equality

module Theory.Functor.Monoidal.Properties.FromRelativeMonad where

open Category
open DependentMonoidalCategory

RelativeMonad→LaxMonoidalFunctor : {ℓ ℓCt₀ ℓCt₁ : Level}
                                 → {CtMonCat : DependentMonoidalCategory {ℓDep₀ = ℓCt₀} {ℓDep₁ = ℓCt₁} (SetMonCat {ℓ})}
                                 → {T : Obj (DependentMonoidalCategory.DepCat CtMonCat) → Obj (SetCat {ℓ})}
                                 → RelativeMonad T (forgetful-functor CtMonCat)
                                 → LaxMonoidalFunctor (DepMonCat CtMonCat) (SetMonCat {ℓ})
RelativeMonad→LaxMonoidalFunctor {ℓ} {ℓCt₀} {ℓCt₁} {CtMonCat} {T} monad
  = laxMonoidalFunctor FunctorT unit-map ap-map {!!} {!!} {!!}
  where
    open RelativeMonad monad
    open Functor FunctorT
    open MonoidalCategory hiding ( Hom )

    unit-map : MonoidalCategory.Hom SetMonCat (unit SetMonCat) (F₀ (unit (DepMonCat CtMonCat)))
    unit-map (lift tt) = η (lift tt)

    ap-map : NaturalTransformation [ tensor SetMonCat ]∘[ [ FunctorT ]×[ FunctorT ] ] [ FunctorT ]∘[ tensor (DepMonCat CtMonCat) ]
    ap-map = naturalTransformation η-map {!!}
      where
        η-map : (x : Obj (DepCat CtMonCat) × Obj (DepCat CtMonCat))
              → (T (proj₁ x) × T (proj₂ x))
              → T ([ tensor (DepMonCat CtMonCat) ]₀ x)
        η-map ((α , ct-α) , (β , ct-β)) (Fx , Fy) = kext (λ x → F₁ ((λ y → x , y) , {!!}) Fy) Fx
