
module Theory.Examples.TwoFunctorToAtkeyParameterizedMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
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
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.AtkeyParameterizedMonad
open import Theory.TwoCategory
open import Theory.Examples.TwoCategory
open import Theory.TwoFunctor


open StrictTwoCategory


LaxTwoFunctor→AtkeyFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})) 
  → Functor (S op ×C S ×C LaxTwoFunctor.P₀ F {!!}) (LaxTwoFunctor.P₀ F {!!})
LaxTwoFunctor→AtkeyFunctor F = {!!}

LaxTwoFunctor→AtkeyParameterizedMonad 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})) 
  → AtkeyParameterizedMonad (LaxTwoFunctor.P₀ F {!!}) S (LaxTwoFunctor→AtkeyFunctor F)
LaxTwoFunctor→AtkeyParameterizedMonad {ℓC₀} {ℓC₁} {ℓS₀} {ℓS₁} {S} F = {!!}
