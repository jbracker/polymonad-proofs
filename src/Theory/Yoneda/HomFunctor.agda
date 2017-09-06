
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition
open import Theory.Functor.Application
open import Theory.Functor.Examples.HomFunctor

module Theory.Yoneda.HomFunctor {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} where

open Category
open Theory.Functor.Application.BiFunctor

private
  SetCat = setCategory {ℓC₀ ⊔ ℓC₁}
  _∘C_ = _∘_ C
  _∘Set_ = _∘_ SetCat

-- Definition of the Hom-Functor Hom[A,-] from C to Set.
Hom[_,-] : (a : Obj C) → Functor C SetCat
Hom[_,-] a = constBiFunctor₁ a (homFunctor ℓC₁ C)
