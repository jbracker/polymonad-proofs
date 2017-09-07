
open import Level

open import Theory.Monoid
open import Theory.Category.Examples.Monoid
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.DiscreteHomCat

module Theory.TwoCategory.Examples.Monoid where

monoidTwoCategory : {ℓ ℓM : Level} {M : Set ℓM} → Monoid M → StrictTwoCategory {ℓ} {ℓM} {ℓM}
monoidTwoCategory {ℓ} {ℓM} {M} monoid = discreteHomCatTwoCategory (monoidCategory {ℓ} {ℓM} monoid)
