 
module Polymonad.Composable where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Relation.Nullary -- ¬
open import Relation.Binary.PropositionalEquality -- ≡
open ≡-Reasoning -- begin ≡⟨⟩ ∎

-- Local
open import Haskell
open import Identity
open import Polymonad

-- -----------------------------------------------------------------------------
-- Composable Polymonad
-- -----------------------------------------------------------------------------

open Polymonad.Polymonad

-- Set of laws that need to hold in order for composition of polymonads to work.
record ComposablePolymonad {TyCons : Set} (pm : Polymonad (IdTyCons ⊎ TyCons) idTC) : Set₁ where
  field
    -- Every bind operator that only involves the identity is equivalent to the identity bind operator.
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] pm ▷ idTC) → substBind (lawId pm) (lawId pm) (lawId pm) (pmBind pm b) {α} {β} ≡ bindId {α} {β}
    
    -- There is only one identity bind operators in this polymonad and it can be identified usind the IdBinds datatype.
    lawEqIdBinds : B[ idTC , idTC ] pm ▷ idTC ≡ IdBinds
    
    -- There a no bind operators aside of the identity bind operator that produce values inside of the identity monad.
    idMorph¬∃ : ∀ {M N : IdTyCons ⊎ TyCons} → (∃ λ(M' : TyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : TyCons) → N ≡ inj₂ N') → ¬ (B[ M , N ] pm ▷ idTC)

-- -----------------------------------------------------------------------------
-- Composable Polymonad Accessor Functions
-- -----------------------------------------------------------------------------

cpmPolymonad : ∀ {TyCons : Set} {pm : Polymonad (IdTyCons ⊎ TyCons) idTC} → ComposablePolymonad pm → Polymonad (IdTyCons ⊎ TyCons) idTC
cpmPolymonad {pm = pm} cpm = pm

cpmLawEqId : ∀ {TyCons : Set} {pm : Polymonad (IdTyCons ⊎ TyCons) idTC} → ComposablePolymonad pm → ⟨ pm ▷ idTC ⟩ ≡ Identity
cpmLawEqId {pm = pm} cpm = lawId pm

cpmLawEqBindId = ComposablePolymonad.lawEqBindId
cpmLawEqIdBinds = ComposablePolymonad.lawEqIdBinds
cpmIdMorph¬∃ = ComposablePolymonad.idMorph¬∃

