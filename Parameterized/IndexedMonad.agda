 
module Parameterized.IndexedMonad where

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
open import Haskell
open import Identity
open import Monad renaming ( mBind to monadBind ; mReturn to monadReturn )

record IxMonad (Ixs : Set) (M : Ixs → Ixs → TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} {i j k : Ixs} → M i j α → (α → M j k β) → M i k β
    return : ∀ {α : Type} {i : Ixs} → α → M i i α
    
    lawIdR : ∀ {α β : Type} {i j : Ixs}
           → (a : α) → (k : α → M i j β) 
           → return a >>= k ≡ k a
    lawIdL : ∀ {α : Type} {i j : Ixs}
           → (m : M i j α)
           → m >>= return ≡ m
    lawAssoc : ∀ {α β γ : Type} {i j k l : Ixs}
             → (m : M i j α) → (f : α → M j k β) → (g : β → M k l γ)
             → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g
  
  _>>_ : ∀ {α β : Type} {i j k : Ixs} → M i j α → M j k β → M i k β
  ma >> mb = ma >>= λ a → mb

  bind = _>>=_

data IxMonadTyCons (Ixs : Set) : Set where
  IxMonadTC : Ixs → Ixs → IxMonadTyCons Ixs

data IxMonadBinds (Ixs : Set) : (M N P : IdTyCons ⊎ IxMonadTyCons Ixs) → Set where
  MonadB   : ∀ {i j k} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC j k)) (inj₂ (IxMonadTC i k))
  FunctorB : ∀ {i j} → IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) idTC (inj₂ (IxMonadTC i j))
  ApplyB   : ∀ {i j} → IxMonadBinds Ixs idTC (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC i j))
  ReturnB  : ∀ {i} → IxMonadBinds Ixs idTC idTC (inj₂ (IxMonadTC i i)) 

open IxMonad renaming (bind to mBind; return to mReturn; lawIdR to mLawIdR ; lawIdL to mLawIdL ; lawAssoc to mLawAssoc ) hiding (_>>=_)

bindMonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j k} → (m : IxMonad Ixs M)
          → [ M i j , M j k ]▷ M i k
bindMonad m = mBind m

bindFunctor : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
            → [ M i j , Identity ]▷ M i j
bindFunctor m ma f = mBind m ma (λ a → mReturn m (f a))

bindApply : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i j} → (m : IxMonad Ixs M)
          → [ Identity , M i j ]▷ M i j
bindApply m ma f = mBind m (mReturn m ma) f

bindReturn : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} {i} → (m : IxMonad Ixs M)
           → [ Identity , Identity ]▷ M i i
bindReturn m ma f = mReturn m (f ma)


PhantomIndex : ∀ {Ixs : Set} → (M : Ixs → Ixs → TyCon) → Set₁
PhantomIndex M = ∃ λ(K : TyCon) → ∀ {i j} → M i j ≡ K
    
castPhantomBind : ∀ {Ixs} {i j k : Ixs} {M : Ixs → Ixs → TyCon} 
                → (K : PhantomIndex M) 
                → [ M i j , M j k ]▷ M i k → [ proj₁ K , proj₁ K ]▷ proj₁ K
castPhantomBind (_ , Mij≡K) b {α} {β} = substBind Mij≡K Mij≡K Mij≡K b {α} {β}

castPhantomReturn : ∀ {Ixs} {i : Ixs} {M : Ixs → Ixs → TyCon} 
                  → (K : PhantomIndex M) → {α : Type} 
                  → (α → M i i α) → (α → proj₁ K α)
castPhantomReturn (_ , Mij≡K) {α = α} r = subst (\X → (α → X α)) Mij≡K r

Mij≡Mkl : ∀ {Ixs : Set} → {M : Ixs → Ixs → TyCon} → (K : PhantomIndex M)
        → ∀ {i j k l} → M i j ≡ M k l
Mij≡Mkl (_ , Mij≡K) = trans Mij≡K (sym Mij≡K)

Mij→K : ∀ {Ixs : Set} → {M : Ixs → Ixs → TyCon} → (K : PhantomIndex M)
      → ∀ {i j} → ∀ {α} → M i j α → (proj₁ K) α
Mij→K (K , Mij≡K) {α = α} mij = subst (λ X → X α) Mij≡K mij

K→Mij : ∀ {Ixs : Set} → {M : Ixs → Ixs → TyCon} → (K : PhantomIndex M)
      → ∀ {i j} → ∀ {α} → (proj₁ K) α → M i j α
K→Mij (K , Mij≡K) {α = α} k = subst (λ X → X α) (sym Mij≡K) k

id≡K→Mij∘Mij→K : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndex M)
               → ∀ {i j} → ∀ {α} → {mij : M i j α} 
               → mij ≡ (K→Mij K (Mij→K K mij))
id≡K→Mij∘Mij→K K = x≡subst²x (proj₂ K)

id≡Mij→K∘K→Mij : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndex M)
               → ∀ {i j} → ∀ {α} → {k : (proj₁ K) α} 
               → k ≡ (Mij→K K (K→Mij K {i = i} {j = j} k))
id≡Mij→K∘K→Mij K = x≡subst²x' (proj₂ K)

PhantomIxMonad→Monad : ∀ {Ixs} {M} → Ixs → IxMonad Ixs M → (K : PhantomIndex M) → Monad (proj₁ K)
PhantomIxMonad→Monad {Ixs = Ixs} {M = IxM} i ixMonad K = record
  { _>>=_ = _>>=_
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
      ixReturn : ∀ {α} → α → IxM i i α
      ixReturn = IxMonad.return ixMonad
      
      _>>=ix_ : [ IxM i i , IxM i i ]▷ IxM i i
      _>>=ix_ = IxMonad.bind ixMonad
      
      M : TyCon
      M = proj₁ K
      Mij≡K : IxM i i ≡ proj₁ K
      Mij≡K = proj₂ K
      
      _>>=_ : [ M , M ]▷ M
      _>>=_ = castPhantomBind K (_>>=ix_)
    
      return : ∀ {α : Type} → α → M α
      return {α = α} = castPhantomReturn K {α} ixReturn
      
      commuteBindK→Mij : ∀ {α β} → (k : M α) → (f : α → M β) 
                       → K→Mij K (k >>= f) ≡ K→Mij K k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f)
      commuteBindK→Mij {α = α} {β = β} k f = begin
        K→Mij K (k >>= f) 
          ≡⟨ refl ⟩
        K→Mij K (castPhantomBind K _>>=ix_ k f) 
          ≡⟨ refl ⟩
        K→Mij K (substBind Mij≡K Mij≡K Mij≡K _>>=ix_ {α} {β} k f)
          ≡⟨ cong (λ X → K→Mij K X) (substBindInwardEq _>>=ix_ Mij≡K Mij≡K Mij≡K k f) ⟩
        K→Mij K ( subst (λ X → X β) Mij≡K (_>>=ix_ (subst (λ X → X α) (sym Mij≡K) k) (subst (λ X → (α → X β)) (sym Mij≡K) f)) )
          ≡⟨ refl ⟩
        K→Mij K ( Mij→K K (K→Mij K k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f)) )
          ≡⟨ sym (id≡K→Mij∘Mij→K K) ⟩
        K→Mij K k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f) ∎
        
      commuteBindK→Mij' : {α β γ : Type} → (k : α → M β) → (h : β → M γ)
                        → subst (λ X → α → X γ) (sym Mij≡K) (λ x → k x >>= h) 
                        ≡ (λ x → subst (λ X → α → X β) (sym Mij≡K) k x >>=ix subst (λ X → β → X γ) (sym Mij≡K) h)
      commuteBindK→Mij' {α = α} {β = β} {γ = γ} k h = funExt (λ a → begin
        subst (λ X → α → X γ) (sym Mij≡K) (λ x → k x >>= h) a
          ≡⟨ sym (shiftFunSubst' (sym Mij≡K) a (λ x → k x >>= h)) ⟩
        subst (λ X → X γ) (sym Mij≡K) ((λ x → k x >>= h) a)
          ≡⟨ refl ⟩
        subst (λ X → X γ) (sym Mij≡K) (k a >>= h)
          ≡⟨ commuteBindK→Mij (k a) h ⟩
        subst (λ X → X β) (sym Mij≡K) (k a) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h)
          ≡⟨ cong (λ X → X >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h)) (shiftFunSubst' (sym Mij≡K) a k) ⟩
        subst (λ X → α → X β) (sym Mij≡K) k a >>=ix subst (λ X → β → X γ) (sym Mij≡K) h ∎)

      commuteReturnK→Mij : ∀ {α} → (a : α) → K→Mij K (return a) ≡ ixReturn a
      commuteReturnK→Mij {α = α} a = begin
        K→Mij K (return a) 
          ≡⟨ refl ⟩ 
        K→Mij K (castPhantomReturn K ixReturn a)
          ≡⟨ refl ⟩
        K→Mij K (subst (\X → (α → X α)) Mij≡K ixReturn a)
          ≡⟨ cong (λ X → K→Mij K X) (sym (shiftFunSubst' Mij≡K a ixReturn)) ⟩
        K→Mij K (subst (\X → X α) Mij≡K (ixReturn a))
          ≡⟨ sym (id≡K→Mij∘Mij→K K) ⟩
        ixReturn a ∎

      commuteReturnK→Mij' : ∀ {α} → subst (\X → (α → X α)) (sym Mij≡K) return ≡ ixReturn
      commuteReturnK→Mij' {α = α} = begin
        subst (\X → (α → X α)) (sym Mij≡K) return
          ≡⟨ refl ⟩ 
        subst (\X → (α → X α)) (sym Mij≡K) (castPhantomReturn K ixReturn)
          ≡⟨ refl ⟩
        subst (\X → (α → X α)) (sym Mij≡K) (subst (\X → (α → X α)) Mij≡K ixReturn)
          ≡⟨ sym (f≡subst²f Mij≡K) ⟩
        ixReturn ∎

      lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
      lawIdR {α = α} {β = β} a k = begin
        return a >>= k 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K K (K→Mij K (return a >>= k)) 
          ≡⟨ cong (λ X → Mij→K K X) (commuteBindK→Mij (return a) k) ⟩
        Mij→K K (K→Mij K (return a) >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k)) 
          ≡⟨ cong (λ X → Mij→K K (X >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))) (commuteReturnK→Mij a) ⟩
        Mij→K K (ixReturn a >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))
          ≡⟨ cong (λ X → Mij→K K X) (IxMonad.lawIdR ixMonad a (subst (λ X → (α → X β)) (sym Mij≡K) k)) ⟩
        Mij→K K (subst (λ X → (α → X β)) (sym Mij≡K) k a)
          ≡⟨ (cong (λ X → Mij→K K X) (sym (shiftFunSubst' (sym Mij≡K) a k))) ⟩
        Mij→K K (subst (λ X → X β) (sym Mij≡K) (k a))
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        k a ∎
      
      lawIdL : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
      lawIdL {α = α} m = begin
        m >>= return 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K K (K→Mij K (m >>= return)) 
          ≡⟨ cong (λ X → Mij→K K X) (commuteBindK→Mij m return) ⟩
        Mij→K K (K→Mij K m >>=ix (subst (λ X → (α → X α)) (sym Mij≡K) return)) 
          ≡⟨ cong (λ X → Mij→K K (K→Mij K m >>=ix X)) commuteReturnK→Mij' ⟩
        Mij→K K (K→Mij K m >>=ix ixReturn) 
          ≡⟨ cong (λ X → Mij→K K X) (IxMonad.lawIdL ixMonad (K→Mij K m)) ⟩
        Mij→K K (K→Mij K m)
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        m ∎
      
      lawAssoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
      lawAssoc {α = α} {β = β} {γ = γ} m k h = begin
        m >>= (λ x → k x >>= h) 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K K (K→Mij K (m >>= (λ x → k x >>= h))) 
          ≡⟨ cong (λ X → Mij→K K X) (commuteBindK→Mij m (λ x → k x >>= h)) ⟩
        Mij→K K (K→Mij K m >>=ix subst (λ X → (α → X γ)) (sym Mij≡K) (λ x → k x >>= h)) 
          ≡⟨ cong (λ X → Mij→K K (K→Mij K m >>=ix X)) (commuteBindK→Mij' k h) ⟩
        Mij→K K (K→Mij K m >>=ix (λ x → (subst (λ X → (α → X β)) (sym Mij≡K) k) x >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))) 
          ≡⟨ cong (λ X → Mij→K K X) (IxMonad.lawAssoc ixMonad (K→Mij K m) ((subst (λ X → (α → X β)) (sym Mij≡K) k)) ((subst (λ X → (β → X γ)) (sym Mij≡K) h))) ⟩
        Mij→K K ((K→Mij K m >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k)) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))
          ≡⟨ cong (λ X → Mij→K K (X >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))) (sym (commuteBindK→Mij m k)) ⟩
        Mij→K K (K→Mij K (m >>= k) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))
          ≡⟨ cong (λ X → Mij→K K X) (sym (commuteBindK→Mij (m >>= k) h)) ⟩
        Mij→K K (K→Mij K ((m >>= k) >>= h))
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        (m >>= k) >>= h ∎
