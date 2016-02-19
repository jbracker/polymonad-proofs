
module KmettMonad.Definition where

-- Stdlib
open import Level
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
open import Functor

-- -----------------------------------------------------------------------------
-- Definition of KmettMonads
-- -----------------------------------------------------------------------------

record KmettMonad {n} (TyCons : Set n) : Set (lsuc n) where
  field
    ⟨_⟩ : TyCons → TyCon
    
    BindCompat : TyCons → TyCons → Set n
    ReturnCompat : TyCons → Set n

    functor : (M : TyCons) → Functor ⟨ M ⟩

    _◆_ : TyCons → TyCons → TyCons
    
    bind⟨_,_,_⟩ : (M N : TyCons) → BindCompat M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    return⟨_,_⟩ : ∀ {α : Type} → (M : TyCons) → ReturnCompat M → α → ⟨ M ⟩ α

    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (comp : BindCompat N M) → (compR : ReturnCompat N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind⟨ N , M , comp ⟩ (return⟨ N , compR ⟩ a) k) ≡ k a
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (comp : BindCompat M N) → (compR : ReturnCompat N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind⟨ M , N , comp ⟩ m return⟨ N , compR ⟩) ≡ m
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (comp1 : BindCompat M (N ◆ P)) → (comp2 : BindCompat N P)
             → (comp3 : BindCompat (M ◆ N) P) → (comp4 : BindCompat M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind⟨ M , N ◆ P , comp1 ⟩ m (λ x → bind⟨ N , P , comp2 ⟩ (f x) g)) 
               ≡ bind⟨ M ◆ N , P , comp3 ⟩ (bind⟨ M , N , comp4 ⟩ m f) g
    
  sequence⟨_,_,_⟩ : ∀ {α β : Type} → (M N : TyCons) → BindCompat M N → ⟨ M ⟩ α → ⟨ N ⟩ β → ⟨ M ◆ N ⟩ β
  sequence⟨ M , N , comp ⟩ ma mb = bind⟨ M , N , comp ⟩ ma (λ _ → mb)
  
  funcDep = _◆_

open KmettMonad

K⟨_▷_⟩ : ∀ {n} {TyCons : Set n} → KmettMonad TyCons → TyCons → TyCon
K⟨ monad ▷ M ⟩ = ⟨ monad ⟩ M

_◆⟨_⟩_ : ∀ {n} {TyCons : Set n} → TyCons → KmettMonad TyCons → TyCons → TyCons  
_◆⟨_⟩_ M monad N = _◆_ monad M N

-- -----------------------------------------------------------------------------
-- Set to represent bind operations of Kmett Polymonad
-- -----------------------------------------------------------------------------

data KmettBinds {n} {TyCons : Set n} (m : KmettMonad TyCons) : (M N P : IdTyCons ⊎ TyCons) → Set n where
  MonadB   : (M N : TyCons) 
           → BindCompat m M N 
           → KmettBinds m (inj₂ M) (inj₂ N) (inj₂ (M ◆⟨ m ⟩ N))
  FunctorB : (M : TyCons) 
           → KmettBinds m (inj₂ M) idTC (inj₂ M)
  ApplyB   : (M : TyCons) 
           → KmettBinds m idTC (inj₂ M) (inj₂ M)
  ReturnB  : (M : TyCons) 
           → ReturnCompat m M 
           → KmettBinds m idTC idTC (inj₂ M) 

-- -----------------------------------------------------------------------------
-- Bind operations required to implement a Kmett Polymonad
-- -----------------------------------------------------------------------------

bindMonad : ∀ {n} {TyCons : Set n} 
          → (M N : TyCons)
          → (m : KmettMonad TyCons)
          → BindCompat m M N
          → [ K⟨ m ▷ M ⟩ , K⟨ m ▷ N ⟩ ]▷ K⟨ m ▷ M ◆⟨ m ⟩ N ⟩
bindMonad M N monad compat {α} {β} ma f = bind⟨_,_,_⟩ monad M N compat {α} {β} ma f

bindFunctor : ∀ {n} {TyCons : Set n}
            → (M : TyCons)
            → (m : KmettMonad TyCons)
            → [ K⟨ m ▷ M ⟩ , Identity ]▷ K⟨ m ▷ M ⟩
bindFunctor {TyCons = TyCons} M monad {α = α} {β = β} ma f 
  = Functor.fmap (KmettMonad.functor monad M) f ma

bindApply : ∀ {n} {TyCons : Set n} 
          → (M : TyCons) 
          → (m : KmettMonad TyCons)
          → [ Identity , K⟨ m ▷ M ⟩ ]▷ K⟨ m ▷ M ⟩
bindApply M monad ma f = f ma 
  -- subst (λ X → K⟨ monad ▷ X ⟩ β) M◆M≡M (bind⟨_,_,_⟩ monad M M bCompat (return⟨_,_⟩ monad M rCompat ma) f)
  -- (return ma) >>= f

bindReturn : ∀ {n} {TyCons : Set n} 
           → (M : TyCons) 
           → (m : KmettMonad TyCons)
           → ReturnCompat m M
           → [ Identity , Identity ]▷ K⟨ m ▷ M ⟩
bindReturn M monad rCompat ma f = return⟨_,_⟩ monad M rCompat (f ma)
