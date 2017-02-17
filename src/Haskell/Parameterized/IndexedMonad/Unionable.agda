 
module Haskell.Parameterized.IndexedMonad.Unionable where

-- Stdlib
open import Level
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
open import Polymonad.Definition
open import Polymonad.Unionable
open import Haskell.Parameterized.IndexedMonad
open import Haskell.Parameterized.IndexedMonad.Polymonad

open IxMonad renaming (bind to mBind; return to mReturn; law-assoc to mLawAssoc)
open Polymonad

IxMonad→UnionablePolymonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} 
                            → (monad : IxMonad Ixs M)
                            → UnionablePolymonad (IxMonad→Polymonad monad)
IxMonad→UnionablePolymonad {Ixs = Ixs} {M = M'} monad = record 
  { lawEqBindId = lawEqBindId 
  ; lawEqIdBinds = refl 
  ; idMorph¬∃ = idMorph¬∃ 
  } where
    pm = IxMonad→Polymonad monad

    TyCons = IdTyCons ⊎ IxMonadTyCons Ixs
    
    lawEqBindId : {α β : Type}
      → (b : B[ idTC , idTC ] pm ▷ idTC)
      → substBind (law-id pm) (law-id pm) (law-id pm) (bind pm {M = idTC} {N = idTC} {P = idTC} b) {α = α} {β = β} ≡ bindId {α = α} {β = β}
    lawEqBindId IdentB = refl
    
    idMorph¬∃ : {M N : TyCons} 
              → ∃ (λ M' → M ≡ inj₂ M') ⊎ ∃ (λ N' → N ≡ inj₂ N')
              → ¬ B[ M , N ] pm ▷ idTC
    idMorph¬∃ {inj₁ IdentTC} {inj₁ IdentTC} (inj₁ (M' , ())) IdentB
    idMorph¬∃ {inj₁ IdentTC} {inj₁ IdentTC} (inj₂ (N' , ())) IdentB
    idMorph¬∃ {inj₁ IdentTC} {inj₂ (IxMonadTC i j)} p (lift ())
    idMorph¬∃ {inj₂ (IxMonadTC i j)} {inj₁ IdentTC} p (lift ())
    idMorph¬∃ {inj₂ (IxMonadTC i j)} {inj₂ (IxMonadTC k l)} p (lift ())
