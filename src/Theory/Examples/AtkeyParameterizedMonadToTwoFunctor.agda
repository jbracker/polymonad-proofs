
module Theory.Examples.AtkeyParameterizedMonadToTwoFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Utilities
open import Haskell
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor


open Category
open StrictTwoCategory

functor-convert : {ℓ₀ ℓ₁ : Level}
                → {C : Category {ℓ₀} {ℓ₁}} {D : Category {ℓ₀} {ℓ₁}} {E : Category {ℓ₀} {ℓ₁}}
                → D ≡ C → E ≡ C
                → Functor D E → Functor C C
functor-convert refl refl F = F

AtkeyFunctor→LaxTwoFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Category {ℓS₀} {ℓS₁}}
  → {T : Functor (S op ×C S ×C C) C}
  → (F : AtkeyParameterizedMonad C S T) 
  → LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})
AtkeyFunctor→LaxTwoFunctor {C = C} {S} {T} F = {!!}
