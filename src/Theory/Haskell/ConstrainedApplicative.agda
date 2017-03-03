
open import Level

module Theory.Haskell.ConstrainedApplicative where

open import Theory.Haskell.ConstrainedFunctor

record ConstrainedApplicative {ℓ₀ ℓ₁ : Level} (F : ConstrainedFunctor {zero} {ℓ₀} {ℓ₁}) : Set ℓ₁ where

-- TODO
