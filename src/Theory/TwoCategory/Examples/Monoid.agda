
open import Level

open import Theory.Monoid
open import Theory.Category.Examples.Monoid
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.DiscreteHomCat

module Theory.TwoCategory.Examples.Monoid where

monoidTwoCategory : {ℓM : Level} {M : Set ℓM} → Monoid M → StrictTwoCategory {zero} {ℓM} {ℓM}
monoidTwoCategory {ℓM} {M} monoid = discreteHomCatTwoCategory (monoidCategory {ℓM} monoid)
