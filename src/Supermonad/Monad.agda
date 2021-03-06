
module Supermonad.Monad where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding ( _>>=_ ; functor )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Haskell.Functor hiding ( functor )
open import Haskell.Applicative
open import Haskell.Monad hiding ( monad )
open import Haskell.Monad.Polymonad
open import Haskell.Constrained.ConstrainedFunctor
open import Haskell.Parameterized.PhantomIndices
open import Supermonad.Definition 

-- -----------------------------------------------------------------------------
-- Standard Monads are Super Monads
-- -----------------------------------------------------------------------------

Monad→Supermonad : ∀ {ℓ} 
                 → (M : TyCon)
                 → Monad M 
                 → Supermonad (Lift {ℓ = ℓ} MonadTyCons)
Monad→Supermonad {ℓ = ℓ} M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = cfunctor
  ; tyConArity = tyConArity
  ; tyConArgTys = tyConArgTys
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = lawUniqueBind
  ; lawUniqueReturn = lawUniqueReturn
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  } where
    TyCons = Lift {ℓ = ℓ} MonadTyCons
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (lift MonadTC) = M
    
    Binds : TyCons → TyCons → TyCons → Type → Type → Set ℓ
    Binds (lift MonadTC) (lift MonadTC) (lift MonadTC) _ _ = Lift ⊤
    
    Returns : TyCons → Type → Set ℓ
    Returns (lift MonadTC) _ = Lift ⊤
    
    _>>=_ = Monad._>>=_ monad
    return' = Monad.return monad

    tyConArity : ℕ
    tyConArity = 0

    tyConArgTys : Vec (Set ℓ) tyConArity
    tyConArgTys = []
    
    tyCon : ParamTyCon tyConArgTys
    tyCon = lift M

    bind : {α β : Type} → {M N P : TyCons} → Binds M N P α β → ( ⟨ M ⟩ α → ( α → ⟨ N ⟩ β ) → ⟨ P ⟩ β )
    bind {M = lift MonadTC} {N = lift MonadTC} {P = lift MonadTC} (lift tt) ma f = ma >>= f
    
    return : {α : Type} → {M : TyCons} → Returns M α → ( α → ⟨ M ⟩ α )
    return {M = lift MonadTC} (lift tt) = return'
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (lift MonadTC) f ma = ma >>= (return' ∘ f)
    
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc ℓ} (⟨ M ⟩ ≡ X))
    lawSingleTyCon (lift MonadTC) = lift refl
    
    lawUniqueBind : {α β : Type} {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P α β) 
                  → b₁ ≡ b₂
    lawUniqueBind {M = lift MonadTC} {N = lift MonadTC} {P = lift MonadTC} (lift tt) (lift tt) = refl
    
    lawUniqueReturn : {α : Type} {M : TyCons} 
                    → (r₁ r₂ : Returns M α) 
                    → r₁ ≡ r₂
    lawUniqueReturn {M = lift MonadTC} (lift tt) (lift tt) = refl
    
    law-right-id : {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    law-right-id (lift MonadTC) (lift MonadTC) (lift tt) (lift tt) a f = Monad.law-left-id monad a f
    
    law-left-id : {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    law-left-id (lift MonadTC) (lift MonadTC) (lift tt) (lift tt) m = Monad.law-right-id monad m
    
    law-assoc : {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    law-assoc (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift MonadTC) (lift tt) (lift tt) (lift tt) (lift tt) m f g = Monad.law-assoc monad m f g
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (lift MonadTC) = Applicative.functor (Monad.applicative monad)
    
    cfunctor : (M : TyCons) → ConstrainedFunctor {ℓ = ℓ} ⟨ M ⟩
    cfunctor (lift MonadTC) = Functor→ConstrainedFunctor M (functor (lift MonadTC))

    
    law-monad-fmap : {α β : Type}
                 → (M N : TyCons)
                 → (fcts : ConstrainedFunctor.FunctorCts (cfunctor M) α β)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ ConstrainedFunctor.fmap (cfunctor M) fcts f m
    law-monad-fmap (lift MonadTC) (lift MonadTC) fcts (lift tt) (lift tt) f m = sym (Monad.law-monad-fmap monad f m)


Monad→UnconstrainedSupermonad 
  : ∀ {ℓ} → (M : TyCon) → Monad M → UnconstrainedSupermonad (Lift {ℓ = ℓ} MonadTyCons)
Monad→UnconstrainedSupermonad {ℓ = ℓ} M monad = record
  { supermonad = supermonad
  ; lawBindUnconstrained = Binds , lawBindUnconstrained
  ; lawReturnUnconstrained = Returns , lawReturnUnconstrained
  ; lawFunctorUnconstrained = lawFunctorUnconstrained
  } where
    supermonad = Monad→Supermonad {ℓ = ℓ} M monad
    TyCons = Supermonad.tyConSet supermonad
    
    Binds : TyCons → TyCons → TyCons → Set ℓ
    Binds (lift MonadTC) (lift MonadTC) (lift MonadTC) = Lift ⊤
    
    Returns : TyCons → Set ℓ
    Returns (lift MonadTC) = Lift ⊤
    
    lawBindUnconstrained : (α β : Type) → (M N P : TyCons) 
                         → Binds M N P ≡ Supermonad.Binds supermonad M N P α β
    lawBindUnconstrained α β (lift MonadTC) (lift MonadTC) (lift MonadTC) = refl
    
    lawReturnUnconstrained : (α : Type) → (M : TyCons)
                           → Returns M ≡ Supermonad.Returns supermonad M α
    lawReturnUnconstrained α (lift MonadTC) = refl
  
    lawFunctorUnconstrained : (M : TyCons) → Functor K⟨ supermonad ▷ M ⟩
    lawFunctorUnconstrained (lift MonadTC) = Applicative.functor (Monad.applicative monad)
    {-
    lawFunctorUnconstrained : (α β : Type) → (M : TyCons)
                            → Lift {ℓ = ℓ} ⊤ ≡ ConstrainedFunctor.FunctorCts (Supermonad.functor supermonad M) α β
    lawFunctorUnconstrained α β (lift MonadTC) = refl
    -}
