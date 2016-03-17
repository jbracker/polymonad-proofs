
module SuperMonad.Uniqueness where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Functor 
open import SuperMonad.Definition

open SuperMonad.Definition.SuperMonad

SuperMonad→UniqueBind : ∀ {ℓ} {TyCons : Set ℓ} 
                      → (SM : SuperMonad TyCons)
                      → (M N : TyCons)
                      → (b₁ b₂ : SuperMonad.Binds SM M N)
                      → {α β : Type}
                      → bind SM b₁ {α = α} {β = β} ≡ bind SM b₂ {α = α} {β = β}
SuperMonad→UniqueBind {TyCons = TyCons} sm M N b₁ b₂ {α = α} {β = β} = funExt $ λ ma → funExt $ λ f → begin
  bind sm b₁ ma f 
    ≡⟨ {!!} ⟩
  bind sm b₂ ma f ∎


EmptySuperMonad : SuperMonad ⊥
EmptySuperMonad = record
                    { ⟨_⟩ = λ _ z → z
                    ; Binds = λ _ → λ ()
                    ; Returns = λ ()
                    ; functor = λ M →
                                    record
                                    { fmap = λ {α} {β} z → z
                                    ; lawId = λ {α} → refl
                                    ; lawDist = λ {α} {β} {γ} f g → refl
                                    }
                    ; _◆_ = λ _ z → z
                    ; bind = λ {M} {N} _ {α} {β} z z₁ → z₁ z
                    ; return = λ {α} {M} _ z → z
                    ; lawIdR = λ {α} {β} M → λ ()
                    ; lawIdL = λ {α} M → λ ()
                    ; lawAssoc = λ {α} {β} {γ} M N → λ ()
                    }
