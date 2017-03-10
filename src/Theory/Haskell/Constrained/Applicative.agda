
open import Level

module Theory.Haskell.Constrained.Applicative where

open import Theory.Haskell.Constrained.Functor

record ConstrainedApplicative {ℓ₀ ℓ₁ : Level} (F : ConstrainedFunctor {zero} {ℓ₀} {ℓ₁}) : Set ℓ₁ where

-- TODO
