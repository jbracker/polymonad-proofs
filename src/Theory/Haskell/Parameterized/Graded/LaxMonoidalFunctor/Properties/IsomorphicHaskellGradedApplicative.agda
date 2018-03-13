
open import Level
open import Function

open import Data.Product

open import Bijection

open import Haskell
open import Haskell.Parameterized.Graded.Applicative renaming ( GradedApplicative to HaskellGradedApplicative )

open import Theory.Monoid
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Monoidal.Properties.IsomorphicGradedApplicative
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicLaxMonoidalFunctor

module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicHaskellGradedApplicative where  

GradedLaxMonoidalFunctor↔HaskellGradedApplicative : {ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                                  → GradedLaxMonoidalFunctor Mon SetMonCat SetMonCat ↔ (Σ (M → TyCon) (HaskellGradedApplicative Mon))
GradedLaxMonoidalFunctor↔HaskellGradedApplicative {ℓMon} {M} Mon = trans (GradedLaxMonoidalFunctor↔LaxMonoidalFunctor Mon) (LaxMonoidalFunctor↔GradedApplicative Mon)

HaskellGradedApplicative↔GradedLaxMonoidalFunctor : {ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                                  → (Σ (M → TyCon) (HaskellGradedApplicative Mon)) ↔ GradedLaxMonoidalFunctor Mon SetMonCat SetMonCat
HaskellGradedApplicative↔GradedLaxMonoidalFunctor Mon = sym $ GradedLaxMonoidalFunctor↔HaskellGradedApplicative Mon
