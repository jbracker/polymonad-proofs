
module SuperMonad.Definition where

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
open import Polymonad
open import Functor

-- -----------------------------------------------------------------------------
-- Definition of SuperMonads
-- -----------------------------------------------------------------------------

record SuperMonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  field
    ⟨_⟩ : TyCons → TyCon
    
    Binds : TyCons → TyCons → Set ℓ
    Returns : TyCons → Set ℓ

    functor : (M : TyCons) → Functor ⟨ M ⟩

    _◆_ : TyCons → TyCons → TyCons
    
    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    return : ∀ {α : Type} {M : TyCons} → Returns M → α → ⟨ M ⟩ α

    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind {M = N} {N = M} b (return {M = N} r a) k) ≡ k a
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g
    
  sequence : ∀ {α β : Type} {M N : TyCons} → Binds M N → ⟨ M ⟩ α → ⟨ N ⟩ β → ⟨ M ◆ N ⟩ β
  sequence b ma mb = bind b ma (λ _ → mb)
  
  funcDep = _◆_

K⟨_▷_⟩ : ∀ {n} {TyCons : Set n} → SuperMonad TyCons → TyCons → TyCon
K⟨ monad ▷ M ⟩ = SuperMonad.⟨ monad ⟩ M

_◆⟨_⟩_ : ∀ {n} {TyCons : Set n} → TyCons → SuperMonad TyCons → TyCons → TyCons  
_◆⟨_⟩_ M monad N = SuperMonad._◆_ monad M N

-- -----------------------------------------------------------------------------
-- Set to represent bind operations of Super Polymonad
-- -----------------------------------------------------------------------------

data SuperBinds {n} {TyCons : Set n} (m : SuperMonad TyCons) : (M N P : IdTyCons ⊎ TyCons) → Set n where
  MonadB   : (M N : TyCons) 
           → SuperMonad.Binds m M N 
           → SuperBinds m (inj₂ M) (inj₂ N) (inj₂ (M ◆⟨ m ⟩ N))
  FunctorB : (M : TyCons) 
           → SuperBinds m (inj₂ M) idTC (inj₂ M)
  ApplyB   : (M : TyCons) 
           → SuperBinds m idTC (inj₂ M) (inj₂ M)
  ReturnB  : (M : TyCons) 
           → SuperMonad.Returns m M 
           → SuperBinds m idTC idTC (inj₂ M) 

-- -----------------------------------------------------------------------------
-- Bind operations required to implement a Super Polymonad
-- -----------------------------------------------------------------------------

bindMonad : ∀ {n} {TyCons : Set n} 
          → (M N : TyCons)
          → (m : SuperMonad TyCons)
          → SuperMonad.Binds m M N
          → [ K⟨ m ▷ M ⟩ , K⟨ m ▷ N ⟩ ]▷ K⟨ m ▷ M ◆⟨ m ⟩ N ⟩
bindMonad M N monad b {α} {β} ma f = SuperMonad.bind monad b {α} {β} ma f

bindFunctor : ∀ {n} {TyCons : Set n}
            → (M : TyCons)
            → (m : SuperMonad TyCons)
            → [ K⟨ m ▷ M ⟩ , Identity ]▷ K⟨ m ▷ M ⟩
bindFunctor {TyCons = TyCons} M monad {α = α} {β = β} ma f 
  = Functor.fmap (SuperMonad.functor monad M) f ma

bindApply : ∀ {n} {TyCons : Set n} 
          → (M : TyCons) 
          → (m : SuperMonad TyCons)
          → [ Identity , K⟨ m ▷ M ⟩ ]▷ K⟨ m ▷ M ⟩
bindApply M monad ma f = f ma

bindReturn : ∀ {n} {TyCons : Set n} 
           → (M : TyCons) 
           → (m : SuperMonad TyCons)
           → SuperMonad.Returns m M
           → [ Identity , Identity ]▷ K⟨ m ▷ M ⟩
bindReturn M monad r ma f = SuperMonad.return monad r (f ma)
