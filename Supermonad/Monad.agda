
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
open import Data.Vec hiding ( _>>=_ )
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
open import Parameterized.PhantomIndices
open import Supermonad.Definition 

-- -----------------------------------------------------------------------------
-- Standard Monads are Super Monads
-- -----------------------------------------------------------------------------

Monad→Supermonad : (M : TyCon)
                 → Monad M → Supermonad MonadTyCons
Monad→Supermonad M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; tyConArity = tyConArity
  ; tyConArgTys = tyConArgTys
  ; tyCon = tyCon
  ; bind = bind
  ; return = return
  ; lawSingleTyCon = lawSingleTyCon
  ; lawUniqueBind = lawUniqueBind
  ; lawUniqueReturn = lawUniqueReturn
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = MonadTyCons
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ MonadTC = M
    
    Binds : TyCons → TyCons → TyCons → Type → Type → Set
    Binds MonadTC MonadTC MonadTC _ _ = ⊤
    
    Returns : TyCons → Type → Set
    Returns MonadTC _ = ⊤
    
    _>>=_ = Monad._>>=_ monad
    return' = Monad.return monad

    tyConArity : ℕ
    tyConArity = 0

    tyConArgTys : Vec Set tyConArity
    tyConArgTys = []
    
    tyCon : ParamTyCon tyConArgTys
    tyCon = lift M

    bind : {α β : Type} → {M N P : TyCons} → Binds M N P α β → ( ⟨ M ⟩ α → ( α → ⟨ N ⟩ β ) → ⟨ P ⟩ β )
    bind {M = MonadTC} {N = MonadTC} {P = MonadTC} tt ma f = ma >>= f
    
    return : {α : Type} → {M : TyCons} → Returns M α → ( α → ⟨ M ⟩ α )
    return {M = MonadTC} tt = return'
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ MonadTC f ma = ma >>= (return' ∘ f)
    
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc lzero} (⟨ M ⟩ ≡ X))
    lawSingleTyCon MonadTC = lift refl
    
    lawUniqueBind : {α β : Type} {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P α β) 
                  → b₁ ≡ b₂
    lawUniqueBind {M = MonadTC} {N = MonadTC} {P = MonadTC} tt tt = refl
    
    lawUniqueReturn : {α : Type} {M : TyCons} 
                    → (r₁ r₂ : Returns M α) 
                    → r₁ ≡ r₂
    lawUniqueReturn {M = MonadTC} tt tt = refl
    
    lawIdR : {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N α β) → (r : Returns M α)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    lawIdR MonadTC MonadTC tt tt a f = Monad.lawIdR monad a f
    
    lawIdL : {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M α α) → (r : Returns N α)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    lawIdL MonadTC MonadTC tt tt m = Monad.lawIdL monad m
    
    lawAssoc : {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P α γ) → (b₂ : Binds S T N β γ)
             → (b₃ : Binds N T P β γ) → (b₄ : Binds M S N α β)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    lawAssoc MonadTC MonadTC MonadTC MonadTC MonadTC tt tt tt tt m f g = Monad.lawAssoc monad m f g
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor MonadTC = Applicative.functor (Monad.applicative monad)
    
    lawMonadFmap : {α β : Type}
                 → (M N : TyCons)
                 → (b : Binds M N M α β) → (r : Returns N β)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ Functor.fmap (functor M) f m
    lawMonadFmap MonadTC MonadTC tt tt f m = sym (Monad.lawMonadFmap monad f m)


Monad→UnconstrainedSupermonad 
  : (M : TyCon) → Monad M → UnconstrainedSupermonad MonadTyCons
Monad→UnconstrainedSupermonad M monad = record
  { supermonad = supermonad
  ; lawBindUnconstrained = Binds , lawBindUnconstrained
  ; lawReturnUnconstrained = Returns , lawReturnUnconstrained
  } where
    supermonad = Monad→Supermonad M monad
    TyCons = Supermonad.tyConSet supermonad
    
    Binds : TyCons → TyCons → TyCons → Set
    Binds MonadTC MonadTC MonadTC = ⊤
    
    Returns : TyCons → Set
    Returns MonadTC = ⊤
    
    lawBindUnconstrained : (α β : Type) → (M N P : TyCons) 
                         → Binds M N P ≡ Supermonad.Binds supermonad M N P α β
    lawBindUnconstrained α β MonadTC MonadTC MonadTC = refl
    
    lawReturnUnconstrained : (α : Type) → (M : TyCons)
                           → Returns M ≡ Supermonad.Returns supermonad M α
    lawReturnUnconstrained α MonadTC = refl


{-
Monad→HaskSuperMonad : (M : TyCon)
                     → Monad M → HaskSuperMonad MonadTyCons
Monad→HaskSuperMonad M monad = record
  { supermonad = Monad→SuperMonad M monad
  ; lawUniqueBind = lawUniqueBind
  ; lawCommuteFmapBind = lawCommuteFmapBind
  ; lawDecomposeFmapIntro = lawDecomposeFmapIntro
  } where
    supermonad : SuperMonad MonadTyCons
    supermonad = Monad→SuperMonad M monad
    
    TyCons = MonadTyCons
    Binds = SuperMonad.Binds supermonad
    ⟨_⟩ = SuperMonad.⟨_⟩ supermonad
    bind = SuperMonad.bind supermonad
    functor = SuperMonad.functor supermonad
    _◆_ = SuperMonad._◆_ supermonad
    
    open Functor.Functor
    
    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind b₁ m f ≡ bind b₂ m f
    lawUniqueBind MonadTC MonadTC tt tt m f = refl
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → fmap (functor (M ◆ N)) g (bind b m f) ≡ bind b m (λ x → fmap (functor N) g (f x))
    lawCommuteFmapBind MonadTC MonadTC tt m f g = commuteFmapBind monad m f g
    
    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind b m (g ∘ f) ≡ bind b (fmap (functor M) f m) g
    lawDecomposeFmapIntro MonadTC MonadTC tt m f g = decomposeFmapIntro monad m f g
-}
