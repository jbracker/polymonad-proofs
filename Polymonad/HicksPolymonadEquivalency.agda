
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
open import Polymonad.HicksUniqueBinds using ( uniqueFunctor )
    
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
HicksPolymonad⇒Polymonad hpm = record
  { B[_,_]▷_ = HicksPolymonad.B[_,_]▷_ hpm
  ; ⟨_⟩      = HicksPolymonad.⟨_⟩ hpm
  ; bind     = HicksPolymonad.bind hpm
  ; lawId    = HicksPolymonad.lawId hpm
  ; lawFunctor1 = λ M → proj₁ (HicksPolymonad.lawFunctor hpm M)
  ; lawFunctor2 = λ M b m → trans 
      (cong (λ X → X m (id (HicksPolymonad.lawId hpm))) (uniqueFunctor hpm M b (proj₁ (HicksPolymonad.lawFunctor hpm M)))) 
      (proj₂ (HicksPolymonad.lawFunctor hpm M) m)
  ; lawMorph1   = HicksPolymonad.lawMorph1 hpm
  ; lawMorph2   = HicksPolymonad.lawMorph2 hpm
  ; lawMorph3   = HicksPolymonad.lawMorph3 hpm
  ; lawDiamond1 = HicksPolymonad.lawDiamond1 hpm
  ; lawDiamond2 = HicksPolymonad.lawDiamond2 hpm
  ; lawAssoc    = HicksPolymonad.lawAssoc hpm
  ; lawClosure  = HicksPolymonad.lawClosure hpm
  }

open Polymonad.Polymonad

Polymonad⇒HicksPolymonad : ∀ {TyCons : Set} {Id : TyCons} → Polymonad TyCons Id → HicksPolymonad TyCons Id
Polymonad⇒HicksPolymonad pm = record
  { B[_,_]▷_ = B[_,_]▷_ pm
  ; ⟨_⟩ = ⟨_⟩ pm
  ; bind = bind pm
  ; lawId = lawId pm
  ; lawFunctor = λ M → let b = lawFunctor1 pm M in b , (λ m → lawFunctor2 pm M b m)
  ; lawMorph1 = lawMorph1 pm
  ; lawMorph2 = lawMorph2 pm
  ; lawMorph3 = lawMorph3 pm
  ; lawDiamond1 = lawDiamond1 pm
  ; lawDiamond2 = lawDiamond2 pm
  ; lawAssoc = lawAssoc pm
  ; lawClosure = lawClosure pm
  }
