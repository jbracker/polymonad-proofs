
module Plugin.SubsetSelection where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.String
open import Data.Vec hiding (_∈_)
open import Data.Nat
open import Data.Bool

open import Polymonad
open import Polymonad.Principal

record TyCon : Set where
  field 
    tyConName : String 
    tyConIndices : ℕ

open TyCon

data InstArg : Set where
  conArg : (tc : TyCon) → Vec (ℕ ⊎ TyCon) (tyConIndices tc) → InstArg
  varArg : ℕ → InstArg

record BindInst : Set where
  constructor [_]⇒[_,_]▷_
  field
    Constraints : (ℕ → ℕ ⊎ TyCon) → Bool
    BindTC1 : InstArg
    BindTC2 : InstArg
    BindTC3 : InstArg

subsetSelection 
  : (Binds : Set)
  → (TyCons : Set)
  → (toTyCon : TyCons → TyCon)
  → (toBindInst : Binds → BindInst)
  → SubsetOf Binds × SubsetOf TyCons
subsetSelection Binds TyCons toTyCon toBindInst = {!!}

IsPrincipalPolymonad 
  : ∀ {Binds TyCons : Set} 
  → SubsetOf Binds × SubsetOf TyCons → Set₁
IsPrincipalPolymonad {TyCons = TyCons} (binds , tyCons) 
  = ∃ λ (Id : TyCons) 
  → ∃ λ(Id∈TC : Id ∈ tyCons) 
  → ∃ λ(pm : Polymonad (∃ λ(M : TyCons) → M ∈ tyCons) (Id , Id∈TC)) 
  → PrincipalPM pm

subsetSelectionCorrect 
  : (Binds : Set)
  → (TyCons : Set)
  → (toTyCon : TyCons → TyCon)
  → (toBindInst : Binds → BindInst)
  → IsPrincipalPolymonad (subsetSelection Binds TyCons toTyCon toBindInst)
subsetSelectionCorrect = {!!}

