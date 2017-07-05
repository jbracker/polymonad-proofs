 
open import Level

open import Data.Product

open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Graded.Applicative

open import Theory.Monoid
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Monoidal

module Theory.Functor.Monoidal.Properties.ToGradedApplicative where

open MonoidalFunctor hiding ( F )

MonoidalFunctor→GradedApplicative : {ℓ : Level} {M : Set ℓ} {mon : Monoid M}
                                  → (FMon : MonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {zero}) (setMonoidalCategory {zero}))
                                  → GradedApplicative mon (λ i α → F₀ FMon (i , α))
MonoidalFunctor→GradedApplicative {ℓ} {M} {mon} FMon = graded-applicative {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  where
    F : M → TyCon
    F i α = F₀ FMon (i , α)
