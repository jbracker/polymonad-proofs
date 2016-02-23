
module Parameterized.IndexedMonad.DynState where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Vec hiding ( _>>=_ ; _∈_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Parameterized.IndexedMonad
open import Parameterized.PhantomIndices  

-- -----------------------------------------------------------------------------
-- Definition of the dynamic state monad
-- -----------------------------------------------------------------------------

record DynState (i : Type) (j : Type) (α : Type) : Type where
  constructor DynStateCon
  field
    stateFun : i → j × α

runDynState : {i j α : Type} → DynState i j α → i → j × α
runDynState (DynStateCon sf) i = sf i

execDynState : {i j α : Type} → DynState i j α → i → j
execDynState ma i = proj₁ (runDynState ma i)

evalDynState : {i j α : Type} → DynState i j α → i → α
evalDynState ma i = proj₂ (runDynState ma i)

DynStateMonad : IxMonad Type DynState
DynStateMonad = record
  { _>>=_ = λ ma f → DynStateCon (λ i → let j , a = runDynState ma i in runDynState (f a) j)
  ; return = λ a → DynStateCon (λ s → s , a)
  ; lawIdR = λ a k → refl
  ; lawIdL = λ m → refl
  ; lawAssoc = λ m f g → refl 
  }

-- -----------------------------------------------------------------------------
-- Lifting the universe of DynState
-- -----------------------------------------------------------------------------

LiftDynState : ∀ {ℓ} → Type → Type → Lift {ℓ = ℓ} TyCon
LiftDynState I J = lift (DynState I J)

liftDynStateShift : ∀ {ℓ} {I J : Type} → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ DynState I J
liftDynStateShift = refl

liftDynStateShiftEq : ∀ {ℓ} {I J K L : Type} → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} K L) → DynState I J ≡ DynState K L
liftDynStateShiftEq eq = eq

liftDynStateShiftEq' : ∀ {ℓ} {I J K L : Type} → DynState I J ≡ DynState K L → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} K L)
liftDynStateShiftEq' eq = eq
