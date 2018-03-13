
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Product

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal.Examples.FunctorWithComposition renaming ( functorMonoidalCategory to Fun )
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor
open import Theory.TwoFunctor.Properties.IsomorphicGradedMonad
open import Theory.Haskell.Parameterized.Graded.Monad

module Theory.Functor.Monoidal.Properties.IsomorphicGradedMonad where
 
LaxMonoidalFunctor↔GradedMonad : {ℓMon ℓC₀ ℓC₁ : Level}
                               → {Mon : Set ℓMon}
                               → (C : Category {ℓC₀} {ℓC₁})
                               → (monoid : Monoid Mon)
                               → (LaxMonoidalFunctor (monoidMonoidalCategory monoid) (Fun C)) 
                               ↔ (Σ (Mon → Functor C C) (GradedMonad monoid))
LaxMonoidalFunctor↔GradedMonad C mon = btrans (LaxMonoidalFunctor↔LaxTwoFunctor mon C) (ConstLaxTwoFunctor↔GradedMonad C mon)

GradedMonad↔LaxMonoidalFunctor : {ℓMon ℓC₀ ℓC₁ : Level}
                               → {Mon : Set ℓMon}
                               → (C : Category {ℓC₀} {ℓC₁})
                               → (monoid : Monoid Mon)
                               → (Σ (Mon → Functor C C) (GradedMonad monoid)) 
                               ↔ (LaxMonoidalFunctor (monoidMonoidalCategory monoid) (Fun C)) 
GradedMonad↔LaxMonoidalFunctor C mon = bsym $ LaxMonoidalFunctor↔GradedMonad C mon

