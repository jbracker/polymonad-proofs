
module Supermonad.ConstrainedMonad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding ( _>>=_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Haskell.Functor
open import Haskell.Applicative
open import Haskell.Monad
open import Haskell.Monad.Polymonad
open import Haskell.Constrained.ConstrainedFunctor
open import Haskell.Constrained.ConstrainedMonad
open import Haskell.Parameterized.PhantomIndices
open import Supermonad.Definition 

-- -----------------------------------------------------------------------------
-- Standard Monads are Super Monads
-- -----------------------------------------------------------------------------

ConstrainedMonad→Supermonad : ∀ {ℓ} 
  → (M : TyCon)
  → ConstrainedMonad {ℓ = ℓ} M → Supermonad {ℓ = ℓ} (Lift MonadTyCons)
ConstrainedMonad→Supermonad {ℓ = ℓ} M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; tyConArity = tyConArity
  ; tyConArgTys = tyConArgTys
  ; tyCon = tyCon
  ; bind = λ {α} {β} {M} {N} {P} → bind {α = α} {β = β} {M = M} {N = N} {P = P}
  ; return = λ {α} {M} → return {α = α} {M = M}
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = λ {α} {β} {M} {N} {P} → lawUniqueBind {α} {β} {M} {N} {P} 
  ; lawUniqueReturn = λ {α} {M} → lawUniqueReturn {α} {M}
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  } where
    TyCons = Lift {ℓ = ℓ} MonadTyCons
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (lift MonadTC) = M
    
    Binds : TyCons → TyCons → TyCons → Type → Type → Set ℓ
    Binds (lift MonadTC) (lift MonadTC) (lift MonadTC) α β = ConstrainedMonad.BindCts monad α β
    
    Returns : TyCons → Type → Set ℓ
    Returns (lift MonadTC) α = ConstrainedMonad.ReturnCts monad α
    
    bind' = ConstrainedMonad.bind monad
    return' = ConstrainedMonad.return monad

    tyConArity : ℕ
    tyConArity = 0

    tyConArgTys : Vec (Set ℓ) tyConArity
    tyConArgTys = []
    
    tyCon : ParamTyCon tyConArgTys
    tyCon = lift M

    bind : {α β : Type} → {M N P : TyCons} → Binds M N P α β → ( ⟨ M ⟩ α → ( α → ⟨ N ⟩ β ) → ⟨ P ⟩ β )
    bind {M = lift MonadTC} {N = lift MonadTC} {P = lift MonadTC} b ma f = (bind' b) ma f
    
    return : {α : Type} → {M : TyCons} → Returns M α → ( α → ⟨ M ⟩ α )
    return {M = lift MonadTC} rcts = return' rcts
    
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc ℓ} (⟨ M ⟩ ≡ X))
    lawSingleTyCon (lift MonadTC) = lift refl
    
    lawUniqueBind : {α β : Type} {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P α β) 
                  → b₁ ≡ b₂
    lawUniqueBind {M = lift MonadTC} {N = lift MonadTC} {P = lift MonadTC} b₁ b₂ = ConstrainedMonad.lawUniqueBindCts monad b₁ b₂
    
    lawUniqueReturn : {α : Type} {M : TyCons} 
                    → (r₁ r₂ : Returns M α) 
                    → r₁ ≡ r₂
    lawUniqueReturn {M = lift MonadTC} r₁ r₂ = ConstrainedMonad.lawUniqueReturnCts monad r₁ r₂
    
    law-right-id : {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind {β = β} {M = M} b (return {M = M} r a) k ≡ k a
    law-right-id (lift MonadTC) (lift MonadTC) bcts rcts a f = ConstrainedMonad.law-right-id monad bcts rcts a f
    
    law-left-id : {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind {α = α} {β = α} {M = M} b m (return {M = N} r) ≡ m
    law-left-id (lift MonadTC) (lift MonadTC) bcts rcts m = ConstrainedMonad.law-left-id monad bcts rcts m
    
    law-assoc : {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind {β = γ} {M = M} b₁ m (λ x → bind {β = γ} {M = S} b₂ (f x) g) 
               ≡ bind {β = γ} {M = N} b₃ (bind {β = β} {M = M} b₄ m f) g
    law-assoc {β = β} {γ = γ} (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) b₁ b₂ b₃ b₄ m f g 
      with lawUniqueBind {β} {γ} {lift MonadTC} {lift MonadTC} {lift MonadTC} b₂ b₃
    law-assoc (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) b₁ b₂ .b₂ b₄ m f g | refl 
      = ConstrainedMonad.law-assoc monad b₁ b₂ b₄ m f g
    
    functor : (M : TyCons) → ConstrainedFunctor ⟨ M ⟩
    functor (lift MonadTC) = (ConstrainedMonad.functor monad)
    
    open ConstrainedFunctor
    
    law-monad-fmap : {α β : Type}
                 → (M N : TyCons)
                 → (fcts : FunctorCts (functor M) α β)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind {β = β} {M = M} b m (return {M = N} r ∘ f) ≡ (fmap (functor M) fcts) f m
    law-monad-fmap (lift MonadTC) (lift MonadTC) fcts bcts rcts f m = sym (ConstrainedMonad.law-monad-fmap monad fcts bcts rcts f m)


