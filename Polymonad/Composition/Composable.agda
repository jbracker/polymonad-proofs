 
module Polymonad.Composition.Composable where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad
open import Identity
open import Polymonad.Identity
open import Polymonad.Composable
open import Polymonad.Composition

open Polymonad.Polymonad

-- If we compose two composable polymonads, the result again is a composable polymonad.
polymonadComposableCompose : ∀ {TyCons₁ TyCons₂ : Set}
                           → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
                           → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
                           → (cpm₁ : ComposablePolymonad pm₁)
                           → (cpm₂ : ComposablePolymonad pm₂)
                           → ComposablePolymonad (polymonadCompose cpm₁ cpm₂)
polymonadComposableCompose {TyCons₁} {TyCons₂} {pm₁} {pm₂} cpm₁ cpm₂ = record
  { lawEqBindId = lawEqBindId
  ; lawEqIdBinds = lawEqIdBinds
  ; idMorph¬∃ = idMorph¬∃
  } where
    pm = polymonadCompose cpm₁ cpm₂
    
    TyCons = IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)
    
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] pm ▷ idTC) 
                → substBind (lawId pm) (lawId pm) (lawId pm) (pmBind pm {idTC} {idTC} {idTC} b) {α} {β} ≡ bindId {α} {β}
    lawEqBindId b = cpmLawEqBindId cpm₁ b
    
    lawEqIdBinds : B[ idTC , idTC ] pm ▷ idTC ≡ IdBinds
    lawEqIdBinds = cpmLawEqIdBinds cpm₁
    
    idMorph¬∃ : ∀ {M N : TyCons} 
              → (∃ λ(M' : TyCons₁ ⊎ TyCons₂) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons₁ ⊎ TyCons₂) → N ≡ inj₂ N') 
              → ¬ (B[ M , N ] pm ▷ idTC)
    idMorph¬∃ {inj₁ IdentTC} {inj₁ IdentTC} (inj₁ (M , ())) b
    idMorph¬∃ {inj₁ IdentTC} {inj₁ IdentTC} (inj₂ (N , ())) b
    idMorph¬∃ {inj₁ IdentTC} {inj₂ (inj₁ N₁)} p b = cpmIdMorph¬∃ cpm₁ (inj₂ (N₁ , refl)) b
    idMorph¬∃ {inj₁ IdentTC} {inj₂ (inj₂ N₂)} p b = cpmIdMorph¬∃ cpm₂ (inj₂ (N₂ , refl)) b
    idMorph¬∃ {inj₂ (inj₁ M₁)} {inj₁ IdentTC} p b = cpmIdMorph¬∃ cpm₁ (inj₁ (M₁ , refl)) b
    idMorph¬∃ {inj₂ (inj₁ M₁)} {inj₂ (inj₁ N₁)} p b = cpmIdMorph¬∃ cpm₁ (inj₁ (M₁ , refl)) b
    idMorph¬∃ {inj₂ (inj₁ M₁)} {inj₂ (inj₂ N₂)} p ()
    idMorph¬∃ {inj₂ (inj₂ M₂)} {inj₁ IdentTC} p b = cpmIdMorph¬∃ cpm₂ (inj₁ (M₂ , refl)) b
    idMorph¬∃ {inj₂ (inj₂ M₂)} {inj₂ (inj₁ N₁)} p ()
    idMorph¬∃ {inj₂ (inj₂ M₂)} {inj₂ (inj₂ N₂)} p b = cpmIdMorph¬∃ cpm₂ (inj₁ (M₂ , refl)) b