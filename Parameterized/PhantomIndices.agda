 
module Parameterized.PhantomIndices where

open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Haskell

ParamTyCon : ∀ {n} → (ts : Vec Set n) → Set₁
ParamTyCon [] = TyCon
ParamTyCon (T ∷ ts) = T → ParamTyCon ts

∃Indices : ∀ {n} → (ts : Vec Set n) → (M : ParamTyCon ts) → (TyCon → Set₁) → Set₁
∃Indices [] M pred = pred M
∃Indices (T ∷ ts) M pred = ∃ λ(i : T) → ∃Indices ts (M i) pred

∀Indices : ∀ {n} → (ts : Vec Set n) → (M : ParamTyCon ts) → (TyCon → Set₁) → Set₁
∀Indices [] M pred = pred M
∀Indices (T ∷ ts) M pred = ∀ {i : T} → ∀Indices ts (M i) pred

∀IndicesImpl : ∀ {n} {Accum : TyCon → Set₁} {Result : TyCon → Set₁} 
             → (ts : Vec Set n) 
             → (M : ParamTyCon ts) 
             → ∀Indices ts M Accum 
             → ((X : TyCon) → Accum X → Result X) 
             → ∀Indices ts M Result
∀IndicesImpl [] M assum impl = impl M assum
∀IndicesImpl (I ∷ ts) M accum impl = λ {i : I} → ∀IndicesImpl ts (M i) (accum {i}) impl

PhantomIndices : ∀ {n} (ts : Vec Set n) → (M : ParamTyCon ts) → Set₁
PhantomIndices ts M = ∃ λ(K : TyCon) → ∀Indices ts M (λ X → X ≡ K)

-- We can type case any applied parameterized type constructor into 
-- its representing type constructor.
IxM→K : ∀ {n} 
      → (ts : Vec Set n)
      → {M : ParamTyCon ts} 
      → (K : PhantomIndices ts M)
      → ∀Indices ts M (λ AppM → ∀ {α} → AppM α → (proj₁ K) α)
IxM→K ts {M = M} (K , IxM≡K) = ∀IndicesImpl ts M IxM≡K (λ AppM AppM≡K {α} ma → subst (λ X → X α) AppM≡K ma)

-- We can type case any applied parameterized type constructor into 
-- its representing type constructor.
K→IxM : ∀ {n}
      → (ts : Vec Set n)
      → {M : ParamTyCon ts}
      → (K : PhantomIndices ts M)
      → ∀Indices ts M (λ AppM → ∀ {α} → (proj₁ K) α → AppM α)
K→IxM ts {M = M} (K , IxM≡K) = ∀IndicesImpl ts M IxM≡K (λ AppM AppM≡K {α} k → subst (λ X → X α) (sym AppM≡K) k)

-- Independent of which indices we apply the type parameterized type constructor to it will 
-- always remain the same type.
IxM≡IxM : ∀ {n} 
        → (ts : Vec Set n)
        → {M : ParamTyCon ts} 
        → (K : PhantomIndices ts M)
        → ∀Indices ts M (λ AppM → ∀Indices ts M (λ AppM' → AppM ≡ AppM'))
IxM≡IxM ts {M = M} (_ , IxM≡K) = ∀IndicesImpl ts M IxM≡K (λ AppM AppM≡K → ∀IndicesImpl ts M IxM≡K (λ AppM' AppM'≡K → trans AppM≡K (sym AppM'≡K))) 

