
module Haskell.Monad.Unionable where

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
open import Polymonad.Definition
open import Polymonad.Unionable
open import Haskell.Monad hiding ( monad )
open import Haskell.Monad.Polymonad

Monad→UnionablePolymonad : ∀ {M : TyCon} 
                          → (monad : Monad M)
                          → UnionablePolymonad (Monad→Polymonad monad)
Monad→UnionablePolymonad {M = M'} monad = record 
  { lawEqBindId = lawEqBindId 
  ; lawEqIdBinds = lawEqIdBinds 
  ; idMorph¬∃ = idMorph¬∃ 
  } where
    TyCons = IdTyCons ⊎ MonadTyCons
    
    pm : Polymonad TyCons idTC
    pm = Monad→Polymonad monad
    
    open Polymonad
    
    lawEqBindId : ∀ {α β : Type} → (b : B[ idTC , idTC ] pm ▷ idTC) 
                → substBind (law-id pm) (law-id pm) (law-id pm) (bind pm {M = idTC} {N = idTC} {P = idTC} b) {α} {β} ≡ bindId {α} {β}
    lawEqBindId IdentB = refl
    
    lawEqIdBinds : B[ idTC , idTC ] pm ▷ idTC ≡ IdBinds
    lawEqIdBinds = refl
    
    idMorph¬∃ : ∀ {M N : TyCons} 
              → (∃ λ(M' : MonadTyCons) → M ≡ inj₂ M') ⊎ (∃ λ(N' : MonadTyCons) → N ≡ inj₂ N') 
              → ¬ (B[ M , N ] pm ▷ idTC)
    idMorph¬∃ (inj₁ (M , refl)) ()
    idMorph¬∃ {M = inj₁ IdentTC} (inj₂ (N , refl)) ()
    idMorph¬∃ {M = inj₂ MonadTC} (inj₂ (N , refl)) ()  
