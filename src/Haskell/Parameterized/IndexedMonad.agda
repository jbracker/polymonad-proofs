
open import Level
open import Function renaming ( id to idF )

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
open import Haskell.Functor
open import Haskell.Monad

module Haskell.Parameterized.IndexedMonad where

record IxMonad {ℓ : Level} (Ixs : Set ℓ) (M : Ixs → Ixs → TyCon) : Set (ℓ ⊔ lsuc lzero) where
  field
    _>>=_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    return : {α : Type} {i : Ixs} → α → M i i α

    functor : (i j : Ixs) → Functor (M i j)
    
  open Functor renaming ( fmap to fmap' )
  
  field
    law-right-id : {α β : Type} {i j : Ixs}
           → (a : α) → (k : α → M i j β) 
           → return a >>= k ≡ k a
    law-left-id : ∀ {α : Type} {i j : Ixs}
           → (m : M i j α)
           → m >>= return ≡ m
    law-assoc : {α β γ : Type} {i j k l : Ixs}
             → (m : M i j α) → (f : α → M j k β) → (g : β → M k l γ)
             → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g

    law-monad-fmap : {α β : Type} {i j : Ixs} → (f : α → β) → (ma : M i j α) 
                   → ma >>= (return ∘ f) ≡ fmap' (functor i j) f ma
  
  _>>_ : {α β : Type} {i j k : Ixs} → M i j α → M j k β → M i k β
  ma >> mb = ma >>= λ a → mb
  bind = _>>=_
  
  join : {α : Type} {i j k : Ixs} → M i j (M j k α) → M i k α
  join mma = mma >>= λ x → x

  fmap : {α β : Type} {i j : Ixs} → (α → β) → M i j α → M i j β
  fmap {i = i} {j} f ma = fmap' (functor i j) f ma

data IxMonadTyCons {n} (Ixs : Set n) : Set n where
  IxMonadTC : Ixs → Ixs → IxMonadTyCons Ixs

data IxMonadBinds {n} (Ixs : Set n) : (M N P : IdTyCons ⊎ IxMonadTyCons Ixs) → Set n where
  MonadB   : ∀ {i j k} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC j k)) (inj₂ (IxMonadTC i k))
  FunctorB : ∀ {i j} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) idTC (inj₂ (IxMonadTC i j))
  ApplyB   : ∀ {i j} → IxMonadBinds Ixs idTC (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC i j))
  ReturnB  : ∀ {i} → IxMonadBinds Ixs idTC idTC (inj₂ (IxMonadTC i i)) 

open IxMonad renaming (bind to mBind; return to mReturn; law-right-id to mLawIdR ; law-left-id to mLawIdL ; law-assoc to mLawAssoc ) hiding (_>>=_)

bindMonad : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i j k} → (m : IxMonad Ixs M)
          → [ M i j , M j k ]▷ M i k
bindMonad m = mBind m

bindFunctor : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
            → [ M i j , Identity ]▷ M i j
bindFunctor m ma f = mBind m ma (λ a → mReturn m (f a))

bindApply : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
          → [ Identity , M i j ]▷ M i j
bindApply m ma f = mBind m (mReturn m ma) f

bindReturn : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i} → (m : IxMonad Ixs M)
           → [ Identity , Identity ]▷ M i i
bindReturn m ma f = mReturn m (f ma)


