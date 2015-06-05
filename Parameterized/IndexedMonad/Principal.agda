 
module Parameterized.IndexedMonad.Principal where

-- Stdlib
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
open import Polymonad.Principal
open import Parameterized.IndexedMonad
open import Parameterized.IndexedMonad.Polymonad

open IxMonad renaming (bind to mBind; return to mReturn; lawAssoc to mLawAssoc)
open Polymonad.Polymonad

IxMonad→PrincipalPolymonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} 
                           → (monad : IxMonad Ixs M)
                           → PrincipalPM (IxMonad→Polymonad monad)
IxMonad→PrincipalPolymonad monad F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
IxMonad→PrincipalPolymonad monad F (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ = idTC , IdentB , morph₂ idTC idTC {!!} , morph₁
IxMonad→PrincipalPolymonad monad F (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ = idTC , morph₁ idTC idTC {!!} , IdentB , morph₂
IxMonad→PrincipalPolymonad monad F (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ with (inj₂ (IxMonadTC i j) , idTC) ∈? F
IxMonad→PrincipalPolymonad monad F (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ | yes MI∈F = 
  inj₂ (IxMonadTC i j) , FunctorB , morph₂ (inj₂ (IxMonadTC i j)) idTC MI∈F , morph₁
IxMonad→PrincipalPolymonad monad F (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ | no ¬MI∈F = 
  inj₂ (IxMonadTC i j) , FunctorB , morph₂ (inj₂ (IxMonadTC i j)) idTC {!!} , morph₁
