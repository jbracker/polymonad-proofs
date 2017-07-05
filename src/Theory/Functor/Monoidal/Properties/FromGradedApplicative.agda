 
open import Level

open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Graded.Applicative

open import Theory.Monoid
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Monoidal

module Theory.Functor.Monoidal.Properties.FromGradedApplicative where

GradedApplicative→MonoidalFunctor : {ℓ : Level} {M : Set ℓ} {mon : Monoid M} {F : M → TyCon}
                                  → GradedApplicative mon F → MonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {ℓ}) (setMonoidalCategory {ℓ})
GradedApplicative→MonoidalFunctor {ℓ} {M} {mon} {F} applic = monoidalFunctor {!!} {!!} {!!} {!!}
  where
    
