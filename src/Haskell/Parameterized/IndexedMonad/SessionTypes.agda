
module Parameterized.IndexedMonad.SessionTypes where

-- Stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

-- Local
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.Principal
open import Parameterized.IndexedMonad
open import Parameterized.IndexedMonad.Polymonad


data Types : Set where
  Bool : Types
  Int  : Types

-- Type of sessions
data Session : Set where
  send : Types → Session → Session
  recv : Types → Session → Session
  end  : Session

record SessionM (σ : Session) (τ : Session) (α : Type) : Type where
  field
    content : α

open SessionM

sessionIxMonad : IxMonad Session SessionM
sessionIxMonad = record
  { _>>=_ = bind 
  ; return = return 
  ; law-right-id = λ a k → refl 
  ; law-left-id = λ m → refl 
  ; law-assoc = λ m f g → refl 
  } where
    bind : ∀ {α β : Type} {i j k : Session} 
         → SessionM i j α 
         → (α → SessionM j k β) 
         → SessionM i k β
    bind {β = β} {i = i} {k = k} ma f = let mb = f (content ma) in record { content = content mb }

    return : {α : Type} {i : Session} 
           → α → SessionM i i α
    return a = record { content = a }

sessionPolymonad : Polymonad (IdTyCons ⊎ IxMonadTyCons Session) idTC
sessionPolymonad = IxMonad→Polymonad sessionIxMonad

sessionPrincipalPolymonad : PrincipalPM sessionPolymonad
sessionPrincipalPolymonad F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
sessionPrincipalPolymonad F (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = idTC , IdentB , {!!} , morph₁
sessionPrincipalPolymonad F (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ = idTC , {!!} , IdentB , morph₂
sessionPrincipalPolymonad F (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = {!!} , {!!} , {!!} , {!!}

