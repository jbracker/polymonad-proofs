 
module Parameterized.IndexedMonad where

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
open import Haskell
open import Identity

record IxMonad (Ixs : Set) (M : Ixs → Ixs → TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    return : ∀ {α : Type} {i : Ixs} → α → M i i α
    
    lawIdR : ∀ {α β : Type} {i j : Ixs}
           → (a : α) → (k : α → M i j β) 
           → return a >>= k ≡ k a
    lawIdL : ∀ {α : Type} {i j : Ixs}
           → (m : M i j α)
           → m >>= return ≡ m
    lawAssoc : ∀ {α β γ : Type} {i j k l : Ixs}
             → (m : M i j α) → (f : α → M j k β) → (g : β → M k l γ)
             → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g
  
  _>>_ : ∀ {α β : Type} {i j k : Ixs} → M i j α → M j k β → M i k β
  ma >> mb = ma >>= λ a → mb

  bind = _>>=_

data IxMonadTyCons (Ixs : Set) : Set where
  IxMonadTC : Ixs → Ixs → IxMonadTyCons Ixs

data IxMonadBinds (Ixs : Set) : (M N P : IdTyCons ⊎ IxMonadTyCons Ixs) → Set where
  MonadB   : ∀ {i j k} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC j k)) (inj₂ (IxMonadTC i k))
  FunctorB : ∀ {i j} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) idTC (inj₂ (IxMonadTC i j))
  ApplyB   : ∀ {i j} → IxMonadBinds Ixs idTC (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC i j))
  ReturnB  : ∀ {i} → IxMonadBinds Ixs idTC idTC (inj₂ (IxMonadTC i i)) 

open IxMonad renaming (bind to mBind; return to mReturn)

bindMonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j k} → (m : IxMonad Ixs M)
          → [ M i j , M j k ]▷ M i k
bindMonad m = mBind m

bindFunctor : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
            → [ M i j , Identity ]▷ M i j
bindFunctor m ma f = mBind m ma (λ a → mReturn m (f a))

bindApply : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
          → [ Identity , M i j ]▷ M i j
bindApply m ma f = mBind m (mReturn m ma) f

bindReturn : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i} → (m : IxMonad Ixs M)
           → [ Identity , Identity ]▷ M i i
bindReturn m ma f = mReturn m (f ma)






