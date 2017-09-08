
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Product

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Haskell
open import Haskell.Parameterized.Graded.Monad
open import Theory.Monoid
open import Theory.Category.Monoidal.Examples.FunctorWithComposition renaming ( functorMonoidalCategory to Fun )
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Functor.Monoidal
open import Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor
open import Theory.TwoFunctor.Properties.IsomorphicGradedMonad

module Theory.Functor.Monoidal.Properties.IsomorphicGradedMonad where
 
LaxMonoidalFunctor↔GradedMonad : {ℓE : Level}
                               → {Eff : Set ℓE}
                               → (mon : Monoid Eff)
                               → (LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun SetCat)) 
                               ↔ (Σ (Eff → TyCon) (GradedMonad mon))
LaxMonoidalFunctor↔GradedMonad mon = btrans (LaxMonoidalFunctor↔LaxTwoFunctor mon SetCat) (LaxTwoFunctor↔GradedMonad mon)

GradedMonad↔LaxMonoidalFunctor : {ℓE : Level}
                               → {Eff : Set ℓE}
                               → (mon : Monoid Eff)
                               → (Σ (Eff → TyCon) (GradedMonad mon)) 
                               ↔ (LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun SetCat)) 
GradedMonad↔LaxMonoidalFunctor mon = bsym $ LaxMonoidalFunctor↔GradedMonad mon
