
module KmettMonad.Polymonad where

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
open import KmettMonad.Definition

-- -----------------------------------------------------------------------------
-- Every Kmett Monad is a Polymonad
-- -----------------------------------------------------------------------------

KmettMonad→Polymonad : ∀ {n}
                     → (TyCons : Set n)
                     → KmettMonad TyCons → Polymonad (IdTyCons ⊎ TyCons) idTC
KmettMonad→Polymonad {n = n} KmettTyCons monad = record
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {M} {N} {P} b → bind M N P b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = {!!}
  ; lawMorph2 = {!!}
  ; lawMorph3 = {!!}
  ; lawDiamond1 = {!!}
  ; lawDiamond2 = {!!}
  ; lawAssoc = {!!}
  ; lawClosure = {!!}
  } where
    TyCons = IdTyCons ⊎ KmettTyCons
    Id = idTC
    
    B[_,_]▷_ : (M N P : TyCons) → Set n
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ P       = KmettBinds monad idTC idTC (inj₂ P)
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₂ P       = KmettBinds monad idTC (inj₂ N) (inj₂ P)
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₂ P       = KmettBinds monad (inj₂ M) idTC (inj₂ P)
    B[ inj₂ M       , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₂ N       ]▷ inj₂ P       = KmettBinds monad (inj₂ M) (inj₂ N) (inj₂ P)
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ M) = K⟨ monad ▷ M ⟩
    
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (ReturnB .M rCompat) = bindReturn M monad rCompat
    bind (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (ApplyB .N) = bindApply N monad
    bind (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M) = bindFunctor M monad
    bind (inj₂ M) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₂ N) (inj₂ ._) (MonadB .M .N bCompat) = bindMonad M N monad bCompat

    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ M) = FunctorB M

    lawFunctor2 : ∀ (M : TyCons) → ∀ (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ M) (FunctorB .M) m = begin
      (bind (inj₂ M) Id (inj₂ M) (FunctorB M)) m (id lawId)
        ≡⟨ refl ⟩
      (bindFunctor M monad) m (id lawId)
        ≡⟨ KmettMonad.lawIdL monad M M {!!} {!!} {!!} m ⟩
      m ∎
{-
    -- Paired morphism law from the definition:
    -- ∃ b₁:(M,Id)▷N ∈ Σ ⇔ ∃ b₂:(Id,M)▷N ∈ Σ
    -- and ∀ b₁:(M,Id)▷N, b₂:(Id,M)▷N . b₁ (f v) (λy.y) = b₂ v f

    -- Left to right direction of the paired morphism law equivalancy:
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    -- Right to left direction of the paired morphism law equivalancy:
    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    -- Equation of the paired morphism law:
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind b₁) (f v) (id lawId) ≡ (bind b₂) ((id lawId) v) f
    
    -- Diamond law from the definition:
    -- ( ∃ P, b₁, b₂ . { b₁:(M,N)▷P, b₂:(P,R)▷T } ⊆ Σ ) ⇔
    -- ( ∃ S, b₃, b₄ . { b₃:(N,R)▷S, b₄:(M,S)▷T } ⊆ Σ )
    
    -- Left to right direction of the diamond law equivalancy:
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    -- Right to left direction of the diamond law equivalancy:
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    
    -- Associativity law from the definition:
    -- ∀ b₁, b₂, b₃, b₄ . 
    -- "If" { b₁:(M,N)▷P, b₂:(P,R)▷T, b₃:(N,R)▷S, b₄:(M,S)▷T } ⊆ Σ
    -- "then" b₂ (b₁ m f) g = b₄ m (λ x . b₃ (f x) g)
    lawAssoc : ∀ (M N P R T S : TyCons) 
             → (b₁ : B[ M , N ]▷ P) → (b₂ : B[ P , R ]▷ T) 
             → (b₃ : B[ N , R ]▷ S) → (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind b₂) ((bind b₁) m f) g ≡ (bind b₄) m (λ x → (bind b₃) (f x) g)
    
    -- Closure law from the definition:
    -- "If" ∃ b₁, b₂, b₃, b₄ .
    -- { b₁:(M,N)▷P, b₂:(S,Id)▷M, b₃:(T,Id)▷N, b₄:(P,Id)▷U } ⊆ Σ
    -- "then" ∃ b . b:(S,T)▷U ∈ Σ
    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
-}
