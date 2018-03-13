
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
open import Congruence
open import Extensionality
open import Haskell
open import Identity
open import Haskell.Functor hiding ( functor )
open import Haskell.Monad

module Haskell.Parameterized.Indexed.Monad where

record IxMonad {ℓ : Level} (Ixs : Set ℓ) (M : Ixs → Ixs → TyCon) : Set (ℓ ⊔ lsuc lzero) where
  constructor indexed-monad

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

indexed-monad-eq : {ℓ : Level}
  → {Ixs : Set ℓ} 
  → {M : Ixs → Ixs → TyCon}
  → {_>>=₀_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β}
  → {_>>=₁_ : {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β}
  → {return₀ : {α : Type} {i : Ixs} → α → M i i α}
  → {return₁ : {α : Type} {i : Ixs} → α → M i i α}
  → {functor₀ : (i j : Ixs) → Functor (M i j)}
  → {functor₁ : (i j : Ixs) → Functor (M i j)}
  → {law-right-id₀ : {α β : Type} {i j : Ixs} → (a : α) → (k : α → M i j β) → return₀ a >>=₀ k ≡ k a}
  → {law-right-id₁ : {α β : Type} {i j : Ixs} → (a : α) → (k : α → M i j β) → return₁ a >>=₁ k ≡ k a}
  → {law-left-id₀ : ∀ {α : Type} {i j : Ixs} → (m : M i j α) → m >>=₀ return₀ ≡ m}
  → {law-left-id₁ : ∀ {α : Type} {i j : Ixs} → (m : M i j α) → m >>=₁ return₁ ≡ m}
  → {law-assoc₀ : {α β γ : Type} {i j k l : Ixs} → (m : M i j α) → (f : α → M j k β) → (g : β → M k l γ) → m >>=₀ (λ x → f x >>=₀ g) ≡ (m >>=₀ f) >>=₀ g}
  → {law-assoc₁ : {α β γ : Type} {i j k l : Ixs} → (m : M i j α) → (f : α → M j k β) → (g : β → M k l γ) → m >>=₁ (λ x → f x >>=₁ g) ≡ (m >>=₁ f) >>=₁ g}
  → {law-monad-fmap₀ : {α β : Type} {i j : Ixs} → (f : α → β) → (ma : M i j α) → ma >>=₀ (return₀ ∘ f) ≡ Functor.fmap (functor₀ i j) f ma}
  → {law-monad-fmap₁ : {α β : Type} {i j : Ixs} → (f : α → β) → (ma : M i j α) → ma >>=₁ (return₁ ∘ f) ≡ Functor.fmap (functor₁ i j) f ma}
  → (λ {a} {b} {i} {j} {k} → _>>=₀_ {a} {b} {i} {j} {k}) ≡ _>>=₁_
  → (λ {a} {i} → return₀ {a} {i}) ≡ return₁
  → functor₀ ≡ functor₁
  → indexed-monad {Ixs = Ixs} {M = M} _>>=₀_ return₀ functor₀ law-right-id₀ law-left-id₀ law-assoc₀ law-monad-fmap₀ 
  ≡ indexed-monad _>>=₁_ return₁ functor₁ law-right-id₁ law-left-id₁ law-assoc₁ law-monad-fmap₁
indexed-monad-eq {ℓ} {Ixs} {M} {_>>=_} {._} {return} {._} {functor} {._} {ri₀} {ri₁} {li₀} {li₁} {as₀} {as₁} {mf₀} {mf₁} refl refl refl = cong₄ (indexed-monad _>>=_ return functor) p1 p2 p3 p4
  where
    p1 : (λ {a} {b} {i} {j} → ri₀ {a} {b} {i} {j}) ≡ ri₁
    p1 = implicit-fun-ext 
       $ λ α → implicit-fun-ext 
       $ λ β → implicit-fun-ext 
       $ λ i → implicit-fun-ext 
       $ λ j → fun-ext 
       $ λ a → fun-ext 
       $ λ k → proof-irrelevance (ri₀ {α} {β} {i} {j} a k) (ri₁ {α} {β} {i} {j} a k)
    
    p2 : (λ {a} {i} {j} → li₀ {a} {i} {j}) ≡ li₁
    p2 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ i → implicit-fun-ext 
       $ λ j → fun-ext 
       $ λ m → proof-irrelevance (li₀ {a} {i} {j} m) (li₁ {a} {i} {j} m)
    
    p3 : (λ {a} {b} {c} {i} {j} {k} {l} → as₀ {a} {b} {c} {i} {j} {k} {l}) ≡ as₁
    p3 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ c → implicit-fun-ext 
       $ λ i → implicit-fun-ext 
       $ λ j → implicit-fun-ext 
       $ λ k → implicit-fun-ext 
       $ λ l → fun-ext 
       $ λ m → fun-ext 
       $ λ f → fun-ext 
       $ λ g → proof-irrelevance (as₀ {a} {b} {c} {i} {j} {k} {l} m f g) (as₁ {a} {b} {c} {i} {j} {k} {l} m f g)
    
    p4 : (λ {a} {b} {i} {j} → mf₀ {a} {b} {i} {j}) ≡ mf₁
    p4 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ i → implicit-fun-ext 
       $ λ j → fun-ext 
       $ λ f → fun-ext 
       $ λ m → proof-irrelevance (mf₀ {a} {b} {i} {j} f m) (mf₁ {a} {b} {i} {j} f m)

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


