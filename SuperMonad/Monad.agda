
module SuperMonad.Monad where

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
open import Applicative
open import Monad
open import Monad.Polymonad
open import Polymonad
open import SuperMonad.Definition 

-- -----------------------------------------------------------------------------
-- Standard Monads are Super Monads
-- -----------------------------------------------------------------------------

Monad→SuperMonad : (M : TyCon)
                 → Monad M → SuperMonad MonadTyCons
Monad→SuperMonad M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = bind
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = MonadTyCons
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ MonadTC = M
    
    Binds : TyCons → TyCons → Set
    Binds MonadTC MonadTC = ⊤
    
    Returns : TyCons → Set
    Returns MonadTC = ⊤

    _◆_ : TyCons → TyCons → TyCons
    MonadTC ◆ MonadTC = MonadTC
    
    _>>=_ = Monad._>>=_ monad
    return' = Monad.return monad

    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {M = MonadTC} {N = MonadTC} tt ma f = ma >>= f
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = MonadTC} tt = return'
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ MonadTC f ma = ma >>= (return' ∘ f)
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind b (return r a) k) ≡ k a
    lawIdR MonadTC MonadTC refl tt tt a f = Monad.lawIdR monad a f
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawIdL MonadTC MonadTC refl tt tt m = Monad.lawIdL monad m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g
    lawAssoc MonadTC MonadTC MonadTC refl tt tt tt tt m f g = Monad.lawAssoc monad m f g
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor MonadTC = Applicative.functor (Monad.applicative monad)
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (M◆N≡M : M ◆ N ≡ M)
                 → (b : Binds M N) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → subst (λ X → ⟨ X ⟩ β) M◆N≡M (bind b m (return r ∘ f)) 
                   ≡ Functor.fmap (functor M) f m
    lawMonadFmap MonadTC MonadTC refl tt tt f m = sym (Monad.lawMonadFmap monad f m)
