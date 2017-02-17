 
module Haskell.Parameterized.IndexedMonad.PhantomMonad where

-- Stdlib
open import Level
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Vec hiding ( _>>=_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Identity
open import Haskell.Applicative
open import Haskell.Monad
open import Haskell.Monad.Polymonad
open import Haskell.Monad.Principal
open import Haskell.Monad.Unionable
open import Polymonad.Definition
open import Polymonad.Principal
open import Polymonad.Unionable
open import Haskell.Parameterized.IndexedMonad
open import Haskell.Parameterized.PhantomIndices

open Monad hiding ( _>>=_ ; law-right-id ; law-left-id ; law-assoc ) renaming ( bind to monadBind ; return to monadReturn )

open IxMonad renaming (bind to mBind; return to mReturn; law-right-id to mLawIdR ; law-left-id to mLawIdL ; law-assoc to mLawAssoc ) hiding (_>>=_)

LiftM : ∀ {ℓ} {Ixs : Set ℓ} → (M : Ixs → Ixs → TyCon) → (Ixs → Ixs → Lift {ℓ = suc ℓ} TyCon)
LiftM M I J = lift (M I J)

castPhantomBind : ∀ {ℓ} {Ixs : Set ℓ} {i j k : Ixs} {M : Ixs → Ixs → TyCon} 
                → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM {ℓ = ℓ} M)) 
                → [ M i j , M j k ]▷ M i k → [ proj₁ K , proj₁ K ]▷ proj₁ K
castPhantomBind (_ , Mij≡K) b {α} {β} = substBind (lower Mij≡K) (lower Mij≡K) (lower Mij≡K) b {α} {β}

castPhantomReturn : ∀ {ℓ} {Ixs : Set ℓ} {i : Ixs} {M : Ixs → Ixs → TyCon} 
                  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M)) → {α : Type} 
                  → (α → M i i α) → (α → proj₁ K α)
castPhantomReturn (_ , Mij≡K) {α = α} r = subst (\X → (α → X α)) (lower Mij≡K) r

id≡K→Mij∘Mij→K : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M))
               → ∀ {i j} → ∀ {α} → {mij : M i j α} 
               → mij ≡ (K→IxM (Ixs ∷ Ixs ∷ []) K (IxM→K (Ixs ∷ Ixs ∷ []) K mij))
id≡K→Mij∘Mij→K K {α = α} {mij = mij} = sym (subst²≡id' (lower (proj₂ K)) (λ M → M α) mij) 

id≡Mij→K∘K→Mij : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M))
               → ∀ {i j} → ∀ {α} → {k : (proj₁ K) α} 
               → k ≡ (IxM→K (Ixs ∷ Ixs ∷ []) K (K→IxM (Ixs ∷ Ixs ∷ []) K {i} {j} k))
id≡Mij→K∘K→Mij K {α = α} {k = k} = sym (subst²≡id (lower (proj₂ K)) (λ M → M α) k)

-- -----------------------------------------------------------------------------
-- A indexed monad with phantom indices is basically equivalent to a normal monad.
-- -----------------------------------------------------------------------------
PhantomIxMonad→Monad : ∀ {Ixs} {M : Ixs → Ixs → TyCon} → Ixs → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M)) → IxMonad Ixs M → Monad (proj₁ K)
PhantomIxMonad→Monad {Ixs = Ixs} {M = IxM} i K ixMonad = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicativeFromMonad _>>=_ return law-right-id law-left-id law-assoc
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = λ f x → refl
  } where
      ixReturn : ∀ {α} → α → IxM i i α
      ixReturn = IxMonad.return ixMonad
      
      _>>=ix_ : [ IxM i i , IxM i i ]▷ IxM i i
      _>>=ix_ = IxMonad.bind ixMonad
      
      M : TyCon
      M = proj₁ K
      Mij≡K : IxM i i ≡ proj₁ K
      Mij≡K = lower (proj₂ K)
      
      _>>=_ : [ M , M ]▷ M
      _>>=_ = castPhantomBind K (_>>=ix_)
    
      IxsL = Ixs ∷ Ixs ∷ []
      
      K→Mij = K→IxM IxsL K
      Mij→K = IxM→K IxsL K
      
      return : ∀ {α : Type} → α → M α
      return {α = α} = castPhantomReturn K {α} ixReturn
      
      commuteBindK→Mij : ∀ {α β} → (k : M α) → (f : α → M β) 
                       → K→IxM IxsL K (k >>= f) ≡ K→IxM IxsL K k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f)
      commuteBindK→Mij {α = α} {β = β} k f = begin
        K→Mij (k >>= f) 
          ≡⟨ refl ⟩
        K→Mij (castPhantomBind K _>>=ix_ k f) 
          ≡⟨ refl ⟩
        K→Mij (substBind Mij≡K Mij≡K Mij≡K _>>=ix_ {α} {β} k f)
          ≡⟨ cong (λ X → K→Mij  X) (substBindInwardEq _>>=ix_ Mij≡K Mij≡K Mij≡K k f) ⟩
        K→Mij ( subst (λ X → X β) Mij≡K (_>>=ix_ (subst (λ X → X α) (sym Mij≡K) k) (subst (λ X → (α → X β)) (sym Mij≡K) f)) )
          ≡⟨ refl ⟩
        K→Mij ( Mij→K (K→Mij k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f)) )
          ≡⟨ sym (id≡K→Mij∘Mij→K K) ⟩
        K→Mij k >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) f) ∎
        
      commuteBindK→Mij' : {α β γ : Type} → (k : α → M β) → (h : β → M γ)
                        → subst (λ X → α → X γ) (sym Mij≡K) (λ x → k x >>= h) 
                        ≡ (λ x → subst (λ X → α → X β) (sym Mij≡K) k x >>=ix subst (λ X → β → X γ) (sym Mij≡K) h)
      commuteBindK→Mij' {α = α} {β = β} {γ = γ} k h = fun-ext (λ a → begin
        subst (λ X → α → X γ) (sym Mij≡K) (λ x → k x >>= h) a
          ≡⟨ sym (shiftFunSubst' (sym Mij≡K) a (λ x → k x >>= h)) ⟩
        subst (λ X → X γ) (sym Mij≡K) ((λ x → k x >>= h) a)
          ≡⟨ refl ⟩
        subst (λ X → X γ) (sym Mij≡K) (k a >>= h)
          ≡⟨ commuteBindK→Mij (k a) h ⟩
        subst (λ X → X β) (sym Mij≡K) (k a) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h)
          ≡⟨ cong (λ X → X >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h)) (shiftFunSubst' (sym Mij≡K) a k) ⟩
        subst (λ X → α → X β) (sym Mij≡K) k a >>=ix subst (λ X → β → X γ) (sym Mij≡K) h ∎)

      commuteReturnK→Mij : ∀ {α} → (a : α) → K→Mij (return a) ≡ ixReturn a
      commuteReturnK→Mij {α = α} a = begin
        K→Mij (return a) 
          ≡⟨ refl ⟩ 
        K→Mij (castPhantomReturn K ixReturn a)
          ≡⟨ refl ⟩
        K→Mij (subst (\X → (α → X α)) Mij≡K ixReturn a)
          ≡⟨ cong (λ X → K→Mij X) (sym (shiftFunSubst' Mij≡K a ixReturn)) ⟩
        K→Mij (subst (\X → X α) Mij≡K (ixReturn a))
          ≡⟨ sym (id≡K→Mij∘Mij→K K) ⟩
        ixReturn a ∎

      commuteReturnK→Mij' : ∀ {α} → subst (\X → (α → X α)) (sym Mij≡K) return ≡ ixReturn
      commuteReturnK→Mij' {α = α} = begin
        subst (\X → (α → X α)) (sym Mij≡K) return
          ≡⟨ refl ⟩ 
        subst (\X → (α → X α)) (sym Mij≡K) (castPhantomReturn K ixReturn)
          ≡⟨ refl ⟩
        subst (\X → (α → X α)) (sym Mij≡K) (subst (\X → (α → X α)) Mij≡K ixReturn)
          ≡⟨ subst²≡id' Mij≡K (\X → (α → X α)) ixReturn ⟩
        ixReturn ∎

      law-left-id : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
      law-left-id {α = α} {β = β} a k = begin
        return a >>= k 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (return a >>= k)) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij (return a) k) ⟩
        Mij→K (K→Mij (return a) >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k)) 
          ≡⟨ cong (λ X → Mij→K (X >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))) (commuteReturnK→Mij a) ⟩
        Mij→K (ixReturn a >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.law-right-id ixMonad a (subst (λ X → (α → X β)) (sym Mij≡K) k)) ⟩
        Mij→K (subst (λ X → (α → X β)) (sym Mij≡K) k a)
          ≡⟨ (cong (λ X → Mij→K X) (sym (shiftFunSubst' (sym Mij≡K) a k))) ⟩
        Mij→K (subst (λ X → X β) (sym Mij≡K) (k a))
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        k a ∎
      
      law-right-id : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
      law-right-id {α = α} m = begin
        m >>= return 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (m >>= return)) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij m return) ⟩
        Mij→K (K→Mij m >>=ix (subst (λ X → (α → X α)) (sym Mij≡K) return)) 
          ≡⟨ cong (λ X → Mij→K (K→Mij m >>=ix X)) commuteReturnK→Mij' ⟩
        Mij→K (K→Mij m >>=ix ixReturn) 
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.law-left-id ixMonad (K→Mij m)) ⟩
        Mij→K (K→Mij m)
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        m ∎
      
      law-assoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
      law-assoc {α = α} {β = β} {γ = γ} m k h = begin
        m >>= (λ x → k x >>= h) 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (m >>= (λ x → k x >>= h))) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij m (λ x → k x >>= h)) ⟩
        Mij→K (K→Mij m >>=ix subst (λ X → (α → X γ)) (sym Mij≡K) (λ x → k x >>= h)) 
          ≡⟨ cong (λ X → Mij→K (K→Mij m >>=ix X)) (commuteBindK→Mij' k h) ⟩
        Mij→K (K→Mij m >>=ix (λ x → (subst (λ X → (α → X β)) (sym Mij≡K) k) x >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))) 
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.law-assoc ixMonad (K→Mij m) ((subst (λ X → (α → X β)) (sym Mij≡K) k)) ((subst (λ X → (β → X γ)) (sym Mij≡K) h))) ⟩
        Mij→K ((K→Mij m >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k)) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))
          ≡⟨ cong (λ X → Mij→K (X >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))) (sym (commuteBindK→Mij m k)) ⟩
        Mij→K (K→Mij (m >>= k) >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))
          ≡⟨ cong (λ X → Mij→K X) (sym (commuteBindK→Mij (m >>= k) h)) ⟩
        Mij→K (K→Mij ((m >>= k) >>= h))
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        (m >>= k) >>= h ∎

-- -----------------------------------------------------------------------------
-- Indexed monads are principal polymonads
-- -----------------------------------------------------------------------------
PhantomIxMonad→Polymonad 
  : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
  → Ixs
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M))
  → (ixMonad : IxMonad Ixs M)
  → Polymonad (IdTyCons ⊎ MonadTyCons) idTC
PhantomIxMonad→Polymonad i K ixMonad = Monad→Polymonad (PhantomIxMonad→Monad i K ixMonad)

PhantomIxMonad→PrincipalPolymonad 
  : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
  → (i : Ixs)
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M))
  → (ixMonad : IxMonad Ixs M)
  → PrincipalPM (PhantomIxMonad→Polymonad i K ixMonad)
PhantomIxMonad→PrincipalPolymonad i K ixMonad = Monad→PrincipalPolymonad (PhantomIxMonad→Monad i K ixMonad)

PhantomIxMonad→UnionablePolymonad 
  : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
  → (i : Ixs)
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) (LiftM M))
  → (ixMonad : IxMonad Ixs M)
  → UnionablePolymonad (PhantomIxMonad→Polymonad i K ixMonad)
PhantomIxMonad→UnionablePolymonad i K ixMonad = Monad→UnionablePolymonad (PhantomIxMonad→Monad i K ixMonad)

