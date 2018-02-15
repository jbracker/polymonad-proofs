
module Hicks.Equivalency where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning

-- Local
open import Utilities
open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Haskell
open import Identity
open import Extensionality
open import Equality
open import Polymonad.Definition
open import Polymonad.Equality
open import Hicks.Polymonad
open import Hicks.Equality
open import Hicks.UniqueBinds using ( uniqueFunctor )
    
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
  ; law-id    = HicksPolymonad.law-id hpm
  ; lawFunctor1 = λ M → proj₁ (HicksPolymonad.lawFunctor hpm M)
  ; lawFunctor2 = λ M b m → trans 
      (cong (λ X → X m (id (HicksPolymonad.law-id hpm))) (uniqueFunctor hpm M b (proj₁ (HicksPolymonad.lawFunctor hpm M)))) 
      (proj₂ (HicksPolymonad.lawFunctor hpm M) m)
  ; lawMorph1   = HicksPolymonad.lawMorph1 hpm
  ; lawMorph2   = HicksPolymonad.lawMorph2 hpm
  ; lawMorph3   = HicksPolymonad.lawMorph3 hpm
  ; lawDiamond1 = HicksPolymonad.lawDiamond1 hpm
  ; lawDiamond2 = HicksPolymonad.lawDiamond2 hpm
  ; law-assoc    = HicksPolymonad.law-assoc hpm
  ; lawClosure  = HicksPolymonad.lawClosure hpm
  }

open Polymonad

Polymonad⇒HicksPolymonad : ∀ {TyCons : Set} {Id : TyCons} → Polymonad TyCons Id → HicksPolymonad TyCons Id
Polymonad⇒HicksPolymonad pm = record
  { B[_,_]▷_ = B[_,_]▷_ pm
  ; ⟨_⟩ = ⟨_⟩ pm
  ; bind = bind pm
  ; law-id = law-id pm
  ; lawFunctor = λ M → let b = lawFunctor1 pm M in b , (λ m → lawFunctor2 pm M b m)
  ; lawMorph1 = lawMorph1 pm
  ; lawMorph2 = lawMorph2 pm
  ; lawMorph3 = lawMorph3 pm
  ; lawDiamond1 = lawDiamond1 pm
  ; lawDiamond2 = lawDiamond2 pm
  ; law-assoc = law-assoc pm
  ; lawClosure = lawClosure pm
  }

Polymonad↔HicksPolymonad : {TyCon : Set} {Id : TyCon} → Polymonad TyCon Id ↔ HicksPolymonad TyCon Id
Polymonad↔HicksPolymonad {TyCon} {Id} = bijection (Polymonad⇒HicksPolymonad {TyCon} {Id}) (HicksPolymonad⇒Polymonad {TyCon} {Id}) eqHPM eqPM
  where
    eqHPM : (b : HicksPolymonad TyCon Id) → Polymonad⇒HicksPolymonad (HicksPolymonad⇒Polymonad b) ≡ b
    eqHPM hpm = hicks-polymonad-eq refl refl hrefl hrefl 
                                   (het-fun-ext hrefl 
                                     (λ M → het-Σ-eq refl (het-implicit-fun-ext hrefl 
                                     (λ α → het-fun-ext hrefl 
                                     (λ m → ≡-to-≅ (proof-irrelevance (lawFunctor2 (HicksPolymonad⇒Polymonad hpm) M (lawFunctor1 (HicksPolymonad⇒Polymonad hpm) M) m) (proj₂ (HicksPolymonad.lawFunctor hpm M) m))))))) 
                                   hrefl hrefl hrefl hrefl hrefl
    
    eqPM : (a : Polymonad TyCon Id) → HicksPolymonad⇒Polymonad (Polymonad⇒HicksPolymonad a) ≡ a
    eqPM pm = polymonad-eq refl refl hrefl hrefl hrefl hrefl hrefl hrefl hrefl hrefl


HicksPolymonad↔Polymonad : {TyCon : Set} {Id : TyCon} → HicksPolymonad TyCon Id ↔ Polymonad TyCon Id 
HicksPolymonad↔Polymonad = bsym Polymonad↔HicksPolymonad
