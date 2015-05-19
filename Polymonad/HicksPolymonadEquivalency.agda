
module Polymonad.HicksPolymonadEquivalency where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.HicksPolymonad
open import Polymonad.HicksUniqueBinds
    
--------------------------------------------------------------------------------
-- Polymonad functor law equivalency proofs
--------------------------------------------------------------------------------

functorLawEquiv⇒ : ∀ {M : TyCon} 
                 → (∃ λ(b : [ M , Identity ]▷ M) → ∀ {α : Type} (m : M α) → b m (id refl) ≡ m)
                 → (∀ (b₁ : [ M , Identity ]▷ M) → (b₂ : [ M , Identity ]▷ M) → ∀ {α β} → b₁ {α} {β} ≡ b₂ {α} {β})
                 → (∀ (b : [ M , Identity ]▷ M) → ∀ {α : Type} (m : M α) → b m (id refl) ≡ m)
functorLawEquiv⇒ (b , funcLaw) b₁≡b₂ ∀b m = trans (cong (λ X → X m (id refl)) (b₁≡b₂ ∀b b)) (funcLaw m)

functorLawEquiv⇐ : ∀ {M : TyCon} (b : [ M , Identity ]▷ M)
                 → (∀ (b : [ M , Identity ]▷ M) → ∀ {α : Type} (m : M α) → b m (id refl) ≡ m)
                 → (∃ λ(b' : [ M , Identity ]▷ M) → ∀ {α : Type} (m : M α) → b' m (id refl) ≡ m)
functorLawEquiv⇐ b ∀funcLaw = b , ∀funcLaw b

HicksPolymonad⇒Polymonad : ∀ {TyCons : Set} {Id : TyCons} → HicksPolymonad TyCons Id → Polymonad TyCons Id
HicksPolymonad⇒Polymonad hpm = {!!}

Polymonad⇒HicksPolymonad : ∀ {TyCons : Set} {Id : TyCons} → Polymonad TyCons Id → HicksPolymonad TyCons Id
Polymonad⇒HicksPolymonad pm = {!!}
