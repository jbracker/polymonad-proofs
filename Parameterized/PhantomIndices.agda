 
module Parameterized.PhantomIndices where

open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Haskell

ParamTyCon : ∀ {n} → (ts : Vec Set n) → Set₁
ParamTyCon [] = TyCon
ParamTyCon (T ∷ ts) = T → ParamTyCon ts

∀IndicesM≡K : ∀ {n} {ts : Vec Set n} → (M : ParamTyCon ts) → (K : TyCon) → Set₁
∀IndicesM≡K {ts = []} M K = M ≡ K
∀IndicesM≡K {ts = T ∷ ts} M K = ∀ {i : T} → ∀IndicesM≡K {ts = ts} (M i) K

PhantomIndices : ∀ {n} {ts : Vec Set n} → (M : ParamTyCon ts) → Set₁
PhantomIndices {ts = ts} M = ∃ λ(K : TyCon) → ∀IndicesM≡K {ts = ts} M K


