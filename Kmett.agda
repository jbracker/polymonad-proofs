
module Kmett where

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
open import Parameterized.IndexedMonad hiding ( bindMonad )


record KmettMonad {n ℓ₁ ℓ₂} (TyCons : Set n) : Set (lsuc (n ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    ⟨_⟩ : TyCons → TyCon
    
    BindCompat : TyCons → TyCons → Set ℓ₁
    ReturnCompat : TyCons → Set ℓ₂

    _◆_ : TyCons → TyCons → TyCons
    
    bind⟨_,_,_⟩ : ∀ {α β : Type} → (M N : TyCons) → BindCompat M N → ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ M ◆ N ⟩ β
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

K⟨_▷_⟩ : ∀ {n ℓ₁ ℓ₂} {TyCons : Set n} → KmettMonad {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} TyCons → TyCons → TyCon
K⟨ monad ▷ M ⟩ = KmettMonad.⟨ monad ⟩ M

_◆⟨_⟩_ : ∀ {n ℓ₁ ℓ₂} {TyCons : Set n} → TyCons → KmettMonad {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} TyCons → TyCons → TyCons  
_◆⟨_⟩_ M monad N = KmettMonad._◆_ monad N M

bindMonad : ∀ {n ℓ₁ ℓ₂} {TyCons : Set n} 
          → (M N : TyCons)
          → (m : KmettMonad {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} TyCons)
          → [ K⟨ m ▷ M ⟩ , K⟨ m ▷ N ⟩ ]▷ K⟨ m ▷ M ◆⟨ m ⟩ N ⟩
bindMonad M N monad ma f = {!!} -- KmettMonad.bind⟨_,_,_⟩ monad M N {!!} {!ma!} {!f!}
{-
bindFunctor : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
            → [ M i j , Identity ]▷ M i j
bindFunctor m ma f = mBind m ma (λ a → mReturn m (f a))

bindApply : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
          → [ Identity , M i j ]▷ M i j
bindApply m ma f = mBind m (mReturn m ma) f

bindReturn : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} {i} → (m : IxMonad Ixs M)
           → [ Identity , Identity ]▷ M i i
bindReturn m ma f = mReturn m (f ma)
-}
IxMonad→KmettMonad : ∀ {n}
                   → (Ixs : Set n)
                   → (M : Ixs → Ixs → TyCon)
                   → IxMonad Ixs M → KmettMonad (IxMonadTyCons Ixs)
IxMonad→KmettMonad {n = n} Ixs M monad = record
  { ⟨_⟩ = ⟨_⟩
  ; BindCompat = BindCompat
  ; ReturnCompat = ReturnCompat
  ; _◆_ = _◆_
  ; bind⟨_,_,_⟩ = bind⟨_,_,_⟩
  ; return⟨_,_⟩ = return⟨_,_⟩
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    TyCons = IxMonadTyCons Ixs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (IxMonadTC i j) = M i j
    
    BindCompat : TyCons → TyCons → Set n
    BindCompat (IxMonadTC i j) (IxMonadTC k l) = j ≡ k
    
    ReturnCompat : TyCons → Set n
    ReturnCompat (IxMonadTC i j) = i ≡ j

    _◆_ : TyCons → TyCons → TyCons
    IxMonadTC i j ◆ IxMonadTC k l = IxMonadTC i l
    
    _>>=_ = IxMonad._>>=_ monad
    return = IxMonad.return monad

    bind⟨_,_,_⟩ : ∀ {α β : Type} → (M N : TyCons) → BindCompat M N → ⟨ M ⟩ α → (α → ⟨ N ⟩ β) → ⟨ M ◆ N ⟩ β
    bind⟨_,_,_⟩ (IxMonadTC i j) (IxMonadTC .j l) refl ma f = ma >>= f
    
    return⟨_,_⟩ : ∀ {α : Type} → (M : TyCons) → ReturnCompat M → α → ⟨ M ⟩ α
    return⟨_,_⟩ (IxMonadTC i .i) refl = return
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (comp : BindCompat N M) → (compR : ReturnCompat N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind⟨ N , M , comp ⟩ (return⟨ N , compR ⟩ a) k) ≡ k a
    lawIdR (IxMonadTC i j) (IxMonadTC .i .i) refl refl refl a f = IxMonad.lawIdR monad a f
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (comp : BindCompat M N) → (compR : ReturnCompat N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind⟨ M , N , comp ⟩ m return⟨ N , compR ⟩) ≡ m
    lawIdL (IxMonadTC i j) (IxMonadTC .j .j) refl refl refl m = IxMonad.lawIdL monad m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (comp1 : BindCompat M (N ◆ P)) → (comp2 : BindCompat N P)
             → (comp3 : BindCompat (M ◆ N) P) → (comp4 : BindCompat M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind⟨ M , N ◆ P , comp1 ⟩ m (λ x → bind⟨ N , P , comp2 ⟩ (f x) g)) 
               ≡ bind⟨ M ◆ N , P , comp3 ⟩ (bind⟨ M , N , comp4 ⟩ m f) g
    lawAssoc (IxMonadTC i j) (IxMonadTC .j k) (IxMonadTC .k l) refl refl refl refl refl m f g = IxMonad.lawAssoc monad m f g



KmettMonad→Polymonad : ∀ {n ℓ₁ ℓ₂}
                     → (TyCons : Set n)
                     → KmettMonad {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} TyCons → Polymonad (IdTyCons ⊎ TyCons) idTC
KmettMonad→Polymonad TyCons monad = record
  { B[_,_]▷_ = {!!}
  ; ⟨_⟩ = {!!}
  ; bind = {!!}
  ; lawId = {!!}
  ; lawFunctor1 = {!!}
  ; lawFunctor2 = {!!}
  ; lawMorph1 = {!!}
  ; lawMorph2 = {!!}
  ; lawMorph3 = {!!}
  ; lawDiamond1 = {!!}
  ; lawDiamond2 = {!!}
  ; lawAssoc = {!!}
  ; lawClosure = {!!}
  }
{-
record Polymonad {l : Level} (TyCons : Set l) (Id : TyCons) : Set (lsuc l) where
  field
    -- Set of bind-operation names for each combination of type constructors.
    B[_,_]▷_ : (M N P : TyCons) → Set l

    -- Interpretation of type constructor names into actual type constructors.
    ⟨_⟩ : TyCons → TyCon
    
    -- Interpretation of bind-operation names into actual bind-operations.
    bind : {M N P : TyCons} → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    
    -- Law of the Id type constructor: Id τ = τ
    lawId : ⟨ Id ⟩ ≡ Identity
    
    -- Functor law from the definition:
    -- There exists a functor bind-operation for each type constructor:
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M 
    -- Every bind-operation in shape of a functor needs to be an identity:
    lawFunctor2 : ∀ (M : TyCons) → ∀ (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind b) m (id lawId) ≡ m
    
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
