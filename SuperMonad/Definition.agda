
module SuperMonad.Definition where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding ( _⊔_ )
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Functor

open import Parameterized.PhantomIndices

-- -----------------------------------------------------------------------------
-- Definition of SuperMonads
-- -----------------------------------------------------------------------------

record SuperMonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  field
    ⟨_⟩ : TyCons → TyCon
    
    -- The constraints/condition that needs to hold for the bind operation.
    Binds : TyCons → TyCons → TyCons → Set ℓ
    
    -- The constraints/condition that needs to hold for the return operation.
    Returns : TyCons → Set ℓ

    -- The functor associated with the supermonad.
    functor : (M : TyCons) → Functor ⟨ M ⟩
    
    -- A supermonad only uses a single type constructor.
    
    -- Arity of the supermonad type constructor.
    tyConArity : ℕ
    -- Argument types of the supermonad type constructor indices.
    tyConArgTys : Vec (Set ℓ) tyConArity
    -- The supermonad type constructor.
    tyCon : ParamTyCon tyConArgTys
    
    -- The bind operation of the supermonad.
    bind : {M N P : TyCons} → Binds M N P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    -- The return operation of the supermonad.
    return : ∀ {α : Type} {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    
    -- The supermonad only uses one type constructor.
    lawSingleTyCon : ∀ (M : TyCons) 
                   → ∃Indices tyConArgTys tyCon (λ X → Lift {ℓ = lsuc ℓ} (⟨ M ⟩ ≡ X))
    
    -- The supermonad only has a single bind operation.
    lawUniqueBind : {M N P : TyCons} 
                  → (b₁ b₂ : Binds M N P) 
                  → b₁ ≡ b₂
    
    -- The supermonad only has a single return operation.
    lawUniqueReturn : {M : TyCons} 
                    → (r₁ r₂ : Returns M) 
                    → r₁ ≡ r₂
    
    -- The supermonad version of the right identity law.
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (b : Binds M N N) → (r : Returns M)
           → (a : α) → (k : α → ⟨ N ⟩ β)
           → bind b (return r a) k ≡ k a
    
    -- The supermonad version of the left identity law.
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (b : Binds M N M) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → bind b m (return r) ≡ m
    
    -- The supermonad version of the associativity law.
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P S T : TyCons)
             → (b₁ : Binds M N P) → (b₂ : Binds S T N)
             → (b₃ : Binds N T P) → (b₄ : Binds M S N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ S ⟩ β) → (g : β → ⟨ T ⟩ γ)
             → bind b₁ m (λ x → bind b₂ (f x) g) ≡ bind b₃ (bind b₄ m f) g
    
    -- The supermonad version of the monad-functor relationship.
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (b : Binds M N M) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → bind b m (return r ∘ f) ≡ Functor.fmap (functor M) f m
    
  sequence : ∀ {α β : Type} {M N P : TyCons} → Binds M N P → ⟨ M ⟩ α → ⟨ N ⟩ β → ⟨ P ⟩ β
  sequence b ma mb = bind b ma (λ _ → mb)

K⟨_▷_⟩ : ∀ {n} {TyCons : Set n} → SuperMonad TyCons → TyCons → TyCon
K⟨ monad ▷ M ⟩ = SuperMonad.⟨ monad ⟩ M
