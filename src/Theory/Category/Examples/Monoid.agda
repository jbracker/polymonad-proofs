
-- Stdlib
open import Level
open import Function

open import Data.Unit hiding ( _≤_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans )

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Monoid
open import Theory.Category.Definition

module Theory.Category.Examples.Monoid where  

-- Category naturally formed by a monoid.
monoidCategory : {ℓM : Level} {M : Set ℓM} → Monoid M → Category {zero} {ℓM}
monoidCategory monoid = record
  { Obj = ⊤
  ; Hom = \_ _ → Monoid.carrier monoid
  ; _∘_ = Monoid._∙_ monoid
  ; id = Monoid.ε monoid
  ; assoc = Monoid.assoc monoid
  ; left-id = Monoid.right-id monoid
  ; right-id = Monoid.left-id monoid
  }
{-
monoidCategory' : {ℓM : Level} {M : Set ℓM} → Monoid M → Category {zero} {ℓM}
monoidCategory' monoid = record
  { Obj = ⊤
  ; Hom = \_ _ → Monoid.carrier monoid
  ; _∘_ = flip $ Monoid._∙_ monoid
  ; id = Monoid.ε monoid
  ; assoc = sym $ Monoid.assoc monoid
  ; left-id = Monoid.left-id monoid
  ; right-id = Monoid.right-id monoid
  }
-}
