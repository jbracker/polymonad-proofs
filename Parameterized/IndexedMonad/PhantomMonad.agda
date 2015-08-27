 
module Parameterized.IndexedMonad.PhantomMonad where

-- Stdlib
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
open import Utilities
open import Haskell
open import Identity
open import Monad renaming ( mBind to monadBind ; mReturn to monadReturn )
open import Monad.Polymonad
open import Monad.Principal
open import Monad.Composable
open import Polymonad
open import Polymonad.Principal
open import Polymonad.Composable
open import Parameterized.IndexedMonad
open import Parameterized.PhantomIndices

open IxMonad renaming (bind to mBind; return to mReturn; lawIdR to mLawIdR ; lawIdL to mLawIdL ; lawAssoc to mLawAssoc ) hiding (_>>=_)
    
castPhantomBind : ∀ {Ixs} {i j k : Ixs} {M : Ixs → Ixs → TyCon} 
                → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M) 
                → [ M i j , M j k ]▷ M i k → [ proj₁ K , proj₁ K ]▷ proj₁ K
castPhantomBind (_ , Mij≡K) b {α} {β} = substBind Mij≡K Mij≡K Mij≡K b {α} {β}

castPhantomReturn : ∀ {Ixs} {i : Ixs} {M : Ixs → Ixs → TyCon} 
                  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M) → {α : Type} 
                  → (α → M i i α) → (α → proj₁ K α)
castPhantomReturn (_ , Mij≡K) {α = α} r = subst (\X → (α → X α)) Mij≡K r

id≡K→Mij∘Mij→K : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M)
               → ∀ {i j} → ∀ {α} → {mij : M i j α} 
               → mij ≡ (K→IxM (Ixs ∷ Ixs ∷ []) K (IxM→K (Ixs ∷ Ixs ∷ []) K mij))
id≡K→Mij∘Mij→K K = x≡subst²x (proj₂ K)

id≡Mij→K∘K→Mij : {Ixs : Set} → {M : Ixs → Ixs → TyCon} 
               → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M)
               → ∀ {i j} → ∀ {α} → {k : (proj₁ K) α} 
               → k ≡ (IxM→K (Ixs ∷ Ixs ∷ []) K (K→IxM (Ixs ∷ Ixs ∷ []) K {i} {j} k))
id≡Mij→K∘K→Mij K = x≡subst²x' (proj₂ K)

-- -----------------------------------------------------------------------------
-- A indexed monad with phantom indices is basically equivalent to a normal monad.
-- -----------------------------------------------------------------------------
PhantomIxMonad→Monad : ∀ {Ixs} {M} → Ixs → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M) → IxMonad Ixs M → Monad (proj₁ K)
PhantomIxMonad→Monad {Ixs = Ixs} {M = IxM} i K ixMonad = record
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
          ≡⟨ sym (f≡subst²f Mij≡K) ⟩
        ixReturn ∎

      lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
      lawIdR {α = α} {β = β} a k = begin
        return a >>= k 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (return a >>= k)) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij (return a) k) ⟩
        Mij→K (K→Mij (return a) >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k)) 
          ≡⟨ cong (λ X → Mij→K (X >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))) (commuteReturnK→Mij a) ⟩
        Mij→K (ixReturn a >>=ix (subst (λ X → (α → X β)) (sym Mij≡K) k))
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.lawIdR ixMonad a (subst (λ X → (α → X β)) (sym Mij≡K) k)) ⟩
        Mij→K (subst (λ X → (α → X β)) (sym Mij≡K) k a)
          ≡⟨ (cong (λ X → Mij→K X) (sym (shiftFunSubst' (sym Mij≡K) a k))) ⟩
        Mij→K (subst (λ X → X β) (sym Mij≡K) (k a))
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        k a ∎
      
      lawIdL : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
      lawIdL {α = α} m = begin
        m >>= return 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (m >>= return)) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij m return) ⟩
        Mij→K (K→Mij m >>=ix (subst (λ X → (α → X α)) (sym Mij≡K) return)) 
          ≡⟨ cong (λ X → Mij→K (K→Mij m >>=ix X)) commuteReturnK→Mij' ⟩
        Mij→K (K→Mij m >>=ix ixReturn) 
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.lawIdL ixMonad (K→Mij m)) ⟩
        Mij→K (K→Mij m)
          ≡⟨ sym (id≡Mij→K∘K→Mij K) ⟩
        m ∎
      
      lawAssoc : ∀ {α β γ : Type} 
             → (m : M α) → (k : α → M β) → (h : β → M γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
      lawAssoc {α = α} {β = β} {γ = γ} m k h = begin
        m >>= (λ x → k x >>= h) 
          ≡⟨ id≡Mij→K∘K→Mij K {i = i} {j = i} ⟩
        Mij→K (K→Mij (m >>= (λ x → k x >>= h))) 
          ≡⟨ cong (λ X → Mij→K X) (commuteBindK→Mij m (λ x → k x >>= h)) ⟩
        Mij→K (K→Mij m >>=ix subst (λ X → (α → X γ)) (sym Mij≡K) (λ x → k x >>= h)) 
          ≡⟨ cong (λ X → Mij→K (K→Mij m >>=ix X)) (commuteBindK→Mij' k h) ⟩
        Mij→K (K→Mij m >>=ix (λ x → (subst (λ X → (α → X β)) (sym Mij≡K) k) x >>=ix (subst (λ X → (β → X γ)) (sym Mij≡K) h))) 
          ≡⟨ cong (λ X → Mij→K X) (IxMonad.lawAssoc ixMonad (K→Mij m) ((subst (λ X → (α → X β)) (sym Mij≡K) k)) ((subst (λ X → (β → X γ)) (sym Mij≡K) h))) ⟩
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
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M)
  → (ixMonad : IxMonad Ixs M)
  → Polymonad (IdTyCons ⊎ MonadTyCons) idTC
PhantomIxMonad→Polymonad i K ixMonad = Monad→Polymonad (PhantomIxMonad→Monad i K ixMonad)

PhantomIxMonad→PrincipalPolymonad 
  : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
  → (i : Ixs)
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M)
  → (ixMonad : IxMonad Ixs M)
  → PrincipalPM (PhantomIxMonad→Polymonad i K ixMonad)
PhantomIxMonad→PrincipalPolymonad i K ixMonad = Monad→PrincipalPolymonad (PhantomIxMonad→Monad i K ixMonad)

PhantomIxMonad→ComposablePolymonad 
  : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
  → (i : Ixs)
  → (K : PhantomIndices (Ixs ∷ Ixs ∷ []) M)
  → (ixMonad : IxMonad Ixs M)
  → ComposablePolymonad (PhantomIxMonad→Polymonad i K ixMonad)
PhantomIxMonad→ComposablePolymonad i K ixMonad = Monad→ComposablePolymonad (PhantomIxMonad→Monad i K ixMonad)

-- -----------------------------------------------------------------------------
-- Indexed monads preserve principality when composed with other indexed monads or normal monads.
-- -----------------------------------------------------------------------------

-- Using the example from Polymonad.Principal.Examples we can not compose indexed monads with phantom indices 
-- with each other and with monads.
