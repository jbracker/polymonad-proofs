
module Theory.Examples.TwoFunctorToAtkeyParameterizedMonad where

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
open import Theory.NaturalTransformation
open import Theory.AtkeyParameterizedMonad
open import Theory.TwoCategory
open import Theory.Examples.TwoCategory
open import Theory.TwoFunctor


open Category
open StrictTwoCategory

functor-convert : {ℓ₀ ℓ₁ : Level}
                → {C : Category {ℓ₀} {ℓ₁}} {D : Category {ℓ₀} {ℓ₁}} {E : Category {ℓ₀} {ℓ₁}}
                → D ≡ C → E ≡ C
                → Functor D E → Functor C C
functor-convert refl refl F = F

LaxTwoFunctor→AtkeyFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})) 
  → (∀ s → LaxTwoFunctor.P₀ F s ≡ C)
  → (∀ {s₀ s₁} → (f g : Hom S s₀ s₁) → [ LaxTwoFunctor.P₁ F {s₀} {s₁} ]₀ f ≡ [ LaxTwoFunctor.P₁ F {s₀} {s₁} ]₀ g) 
  → Functor (S op ×C S ×C C) C
LaxTwoFunctor→AtkeyFunctor {C = C} {S} F eq eqP = functor F₀ {!!} {!!} {!!}
  where
    
    F₀ : Obj (S op ×C S ×C C) → Obj C
    F₀ (s₀ , s₁ , x) = Functor.F₀ (functor-convert (eq s₀) (eq s₁) $ [ LaxTwoFunctor.P₁ F {s₀} {s₁} ]₀ ({!!})) x
    
    F₁ : {a b : Obj ((S op) ×C S ×C C)} → Hom (S op ×C S ×C C) a b → Hom C (F₀ a) (F₀ b)
    F₁ {as₀ , as₁ , ax} {bs₀ , bs₁ , bx} (sf₀ , sf₁ , f) = Functor.F₁ (functor-convert {!eq!} {!!} ([ LaxTwoFunctor.P₁ F {as₁} {bs₁} ]₀ sf₁)) f
  
{-
LaxTwoFunctor→AtkeyParameterizedMonad 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})) 
  → AtkeyParameterizedMonad (LaxTwoFunctor.P₀ F {!!}) S (LaxTwoFunctor→AtkeyFunctor F)
LaxTwoFunctor→AtkeyParameterizedMonad {ℓC₀} {ℓC₁} {ℓS₀} {ℓS₁} {S} F = {!!}
-}
