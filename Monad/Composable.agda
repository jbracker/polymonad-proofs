
module Monad.Composable where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary -- ¬
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.Composable
open import Monad
open import Monad.Polymonad

Monad→ComposablePolymonad : ∀ {M : TyCon} 
                          → (monad : Monad M)
                          → ComposablePolymonad (Monad→Polymonad monad)
Monad→ComposablePolymonad {M = M'} monad = record 
  { lawEqBindId = lawEqBindId 
  ; lawEqIdBinds = lawEqIdBinds 
  ; idMorph¬∃ = idMorph¬∃ 
  } where
    TyCons = IdTyCons ⊎ MonadTyCons
    
    pm : Polymonad TyCons idTC
    pm = Monad→Polymonad monad
    
    open Polymonad.Polymonad
    
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] pm ▷ idTC) 
                → substBind (lawId pm) (lawId pm) (lawId pm) (bind pm {M = idTC} {N = idTC} {P = idTC} b) {α} {β} ≡ bindId {α} {β}
    lawEqBindId IdentB = refl
    
    lawEqIdBinds : B[ idTC , idTC ] pm ▷ idTC ≡ IdBinds
    lawEqIdBinds = refl
    
    idMorph¬∃ : ∀ {M N : TyCons} 
              → (∃ λ(M' : MonadTyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : MonadTyCons) → N ≡ inj₂ N') 
              → ¬ (B[ M , N ] pm ▷ idTC)
    idMorph¬∃ (inj₁ (M , refl)) ()
    idMorph¬∃ {M = inj₁ IdentTC} (inj₂ (N , refl)) ()
    idMorph¬∃ {M = inj₂ MonadTC} (inj₂ (N , refl)) ()  
