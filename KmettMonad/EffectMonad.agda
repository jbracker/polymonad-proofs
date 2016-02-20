
module KmettMonad.EffectMonad where

-- Stdlib
open import Level
open import Function
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
open import Functor
open import Polymonad
open import Parameterized.EffectMonad
open import KmettMonad.Definition

open Parameterized.EffectMonad.Monoid

-- -----------------------------------------------------------------------------
-- Indexed Monads are Kmett Monads
-- -----------------------------------------------------------------------------

EffectMonad→KmettMonad : ∀ {n}
                   → (Effect : Set n)
                   → (EffectMonoid : Monoid Effect)
                   → (M : Effect → TyCon)
                   → EffectMonad Effect {{EffectMonoid}} M → KmettMonad (EffMonadTyCons Effect)
EffectMonad→KmettMonad {n = n} Effect EffectMonoid M monad = record
  { ⟨_⟩ = {!!}
  ; BindCompat = {!!}
  ; ReturnCompat = {!!}
  ; functor = {!!}
  ; _◆_ = {!!}
  ; bind⟨_,_,_⟩ = {!!}
  ; return⟨_,_⟩ = {!!}
  ; lawIdR = {!!}
  ; lawIdL = {!!}
  ; lawAssoc = {!!}
  } where
    
