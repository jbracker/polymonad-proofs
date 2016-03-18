
module SuperMonad.Haskell where

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
open import Polymonad
open import Functor
open import SuperMonad.Definition

{-
record HaskSuperMonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  field
    SM : SuperMonad (IdTyCons ⊎ TyCons)
    
    lawId : ∀ {α} → K⟨ SM ▷ idTC ⟩ α ≡ Identity α
    
    lawFunctorBind : ∀ (M : IdTyCons ⊎ TyCons) 
                   → ∃ λ (b : Binds SM M idTC)
                   → ∃ λ (M◆Id≡M : M ◆⟨ SM ⟩ idTC ≡ M) 
                   → ( ∀ {α β} → (ma : K⟨ SM ▷ M ⟩ α) → (f : α → K⟨ SM ▷ idTC ⟩ β) 
                   → subst (λ X → K⟨ SM ▷ X ⟩ β) M◆Id≡M (bind SM b ma f) ≡ Functor.fmap (functor SM M) (subst (λ X → (α → X)) (lawId {β}) f) ma)
    
    lawApplyBind : ∀ (M : IdTyCons ⊎ TyCons) 
                   → ∃ λ (b : Binds SM idTC M)
                   → ∃ λ (Id◆M≡M : idTC ◆⟨ SM ⟩ M ≡ M) 
                   → ( ∀ {α β} → (ma : K⟨ SM ▷ idTC ⟩ α) → (f : α → K⟨ SM ▷ M ⟩ β) 
                   → subst (λ X → K⟨ SM ▷ X ⟩ β) Id◆M≡M (bind SM b ma f) ≡ f (subst (λ X → X) (lawId {α}) ma))
-}


data IdReturns {ℓ} : Set ℓ where
  IdentR : IdReturns

data FunctorBinds {ℓ} {TyCons : Set ℓ} : (IdTyCons ⊎ TyCons) → (IdTyCons ⊎ TyCons) → Set ℓ where
  FunctorB : (M : TyCons) → FunctorBinds (inj₂ M) idTC
  ApplyB   : (M : TyCons) → FunctorBinds idTC (inj₂ M)

SuperMonad→HaskSuperMonad : ∀ {ℓ} {TyCons : Set ℓ} 
                          → SuperMonad TyCons
                          → SuperMonad (IdTyCons ⊎ TyCons)
SuperMonad→HaskSuperMonad {ℓ = ℓ} {TyCons = TCs} SM = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = λ{M} {N} → bind {M = M} {N = N}
  ; return = λ{α} {M} → return {α = α} {M = M}
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  } where
    TyCons = IdTyCons ⊎ TCs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ M) = K⟨ SM ▷ M ⟩
    
    Binds : TyCons → TyCons → Set ℓ
    Binds (inj₁ IdentTC) (inj₁ IdentTC) = IdBinds
    Binds (inj₁ IdentTC) (inj₂ N) = FunctorBinds idTC (inj₂ N)
    Binds (inj₂ M) (inj₁ IdentTC) = FunctorBinds (inj₂ M) idTC
    Binds (inj₂ M) (inj₂ N) = SuperMonad.Binds SM M N
    
    Returns : TyCons → Set ℓ
    Returns (inj₁ IdentTC) = IdReturns
    Returns (inj₂ M) = SuperMonad.Returns SM M
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (inj₁ IdentTC) = record { fmap = λ {α} {β} z → z ; lawId = λ {α} → refl ; lawDist = λ {α} {β} {γ} f g → refl }
    functor (inj₂ M) = SuperMonad.functor SM M
    
    _◆_ : TyCons → TyCons → TyCons
    inj₁ IdentTC ◆ inj₁ IdentTC = idTC
    inj₁ IdentTC ◆ inj₂ N = inj₂ N
    inj₂ M ◆ inj₁ IdentTC = inj₂ M
    inj₂ M ◆ inj₂ N = inj₂ (M ◆⟨ SM ⟩ N)
    
    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {inj₁ IdentTC} {inj₁ IdentTC} IdentB = bindId
    bind {inj₁ IdentTC} {inj₂ .M} (ApplyB M) = bindApply M SM
    bind {inj₂ .M} {inj₁ IdentTC} (FunctorB M) = bindFunctor M SM
    bind {inj₂ M} {inj₂ N} b = SuperMonad.bind SM {M = M} {N = N} b
    
    return : {α : Type} {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = inj₁ IdentTC} r = λ x → x
    return {M = inj₂ M} r = SuperMonad.return SM r
    
    helper1 : ∀ {M N : TCs} → inj₂ {A = IdTyCons} N ≡ inj₂ {A = IdTyCons} M → N ≡ M
    helper1 {M = M} {N = N} N◆M≡M with N
    helper1 refl | N◆M = refl
   
    helper2 : {α : Type} 
            → (M N : TCs)
            → (M≡N : inj₂ M ≡ inj₂ N)
            → (x : ⟨ inj₂ N ⟩ α)
            → subst (λ X → K⟨ SM ▷ X ⟩ α) (sym (helper1 M≡N)) x ≡ subst (λ X → ⟨ X ⟩ α) (sym M≡N) x
    helper2 M .M refl x = refl
    
    lawIdR : {α β : Type} 
           → (M N : IdTyCons ⊎ TCs)
           → (N◆M≡M : N ◆ M ≡ M)
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β) 
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind {M = N} {N = M} b (return {M = N} r a) k) ≡ k a
    lawIdR (inj₁ IdentTC) (inj₁ IdentTC) refl IdentB IdentR a k = refl
    lawIdR (inj₁ IdentTC) (inj₂ M) () (FunctorB .M) r a k
    lawIdR (inj₂ M) (inj₁ IdentTC) refl (ApplyB .M) IdentR a k = refl
    lawIdR {α = α} {β = β} (inj₂ M) (inj₂ N) N◆M≡M b r a k = begin
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (SuperMonad.bind SM b (SuperMonad.return SM r a) k)
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ β) N◆M≡M X) 
                (sym (subst²≡id' (helper1 N◆M≡M) (λ X → K⟨ SM ▷ X ⟩ β) (SuperMonad.bind SM b (SuperMonad.return SM r a) k))) ⟩
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst (λ X → K⟨ SM ▷ X ⟩ β) (sym (helper1 N◆M≡M)) 
                                         (subst (λ X → K⟨ SM ▷ X ⟩ β) (helper1 N◆M≡M) 
                                                (SuperMonad.bind SM b (SuperMonad.return SM r a) k) ) )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst (λ X → K⟨ SM ▷ X ⟩ β) (sym (helper1 N◆M≡M)) X )) 
                (SuperMonad.lawIdR SM M N (helper1 N◆M≡M) b r a k) ⟩
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst (λ X → K⟨ SM ▷ X ⟩ β) (sym (helper1 N◆M≡M)) (k a) )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ β) N◆M≡M X) (helper2 (N ◆⟨ SM ⟩ M) M N◆M≡M (k a)) ⟩
      subst (λ X → ⟨ X ⟩ β) N◆M≡M (subst (λ X → ⟨ X ⟩ β) (sym N◆M≡M) (k a) )
        ≡⟨ subst²≡id N◆M≡M (λ X → ⟨ X ⟩ β) (k a) ⟩
      k a ∎

    lawIdL : {α : Type}
           → (M N : IdTyCons ⊎ TCs)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α) 
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind {M = M} {N = N} b m (return {M = N} r)) ≡ m
    lawIdL (inj₁ IdentTC) (inj₁ IdentTC) refl IdentB IdentR m = refl
    lawIdL (inj₁ IdentTC) (inj₂ M) () (ApplyB .M) r m
    lawIdL (inj₂ M) (inj₁ IdentTC) refl (FunctorB .M) IdentR m 
      = cong (λ X → X m) (Functor.lawId (SuperMonad.functor SM M))
    lawIdL {α = α} (inj₂ M) (inj₂ N) M◆N≡M b r m = begin
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (SuperMonad.bind SM b m (SuperMonad.return SM r))
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) M◆N≡M X) 
                (sym (subst²≡id' (helper1 M◆N≡M) (λ X → K⟨ SM ▷ X ⟩ α) (SuperMonad.bind SM b m (SuperMonad.return SM r)))) ⟩ 
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst (λ X → K⟨ SM ▷ X ⟩ α) (sym (helper1 M◆N≡M)) 
                                         (subst (λ X → K⟨ SM ▷ X ⟩ α) (helper1 M◆N≡M) 
                                                (SuperMonad.bind SM b m (SuperMonad.return SM r)) ) )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst (λ X → K⟨ SM ▷ X ⟩ α) (sym (helper1 M◆N≡M)) X)) (SuperMonad.lawIdL SM M N (helper1 M◆N≡M) b r m) ⟩ 
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst (λ X → K⟨ SM ▷ X ⟩ α) (sym (helper1 M◆N≡M)) m )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) M◆N≡M X) (helper2 (M ◆⟨ SM ⟩ N) M M◆N≡M m) ⟩ 
      subst (λ X → ⟨ X ⟩ α) M◆N≡M (subst (λ X → ⟨ X ⟩ α) (sym M◆N≡M) m )
        ≡⟨ subst²≡id M◆N≡M (λ X → ⟨ X ⟩ α) m ⟩ 
      m ∎

    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨ inj₁ IdentTC ⟩ = λ x → x
    fmap⟨ inj₂ M ⟩ = Functor.fmap (SuperMonad.functor SM M)
    
    Id◆M≡M : ∀ {N} → idTC ◆ inj₂ N ≡ inj₂ N
    Id◆M≡M = refl
    
    Id◆[N◆P]≡[Id◆N]◆P : ∀ {N P} → idTC ◆ (inj₂ N ◆ inj₂ P) ≡ (idTC ◆ inj₂ N) ◆ inj₂ P 
    Id◆[N◆P]≡[Id◆N]◆P = refl
    
    helper3 : {α : Type} 
            → (M N : TCs)
            → (M≡N : inj₂ M ≡ inj₂ N)
            → (x : ⟨ inj₂ M ⟩ α)
            → subst (λ X → K⟨ SM ▷ X ⟩ α) (helper1 M≡N) x ≡ subst (λ X → ⟨ X ⟩ α) M≡N x
    helper3 M .M refl x = refl
    
    lawAssoc : {α β γ : Type} 
             → (M N P : IdTyCons ⊎ TCs)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P)
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P) 
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ) 
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind {M = M} {N = N ◆ P} b₁ m (λ x → bind {M = N} {N = P} b₂ (f x) g)) 
               ≡ bind {M = M ◆ N} {N = P} b₃ (bind {M = M} {N = N} b₄ m f) g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) refl IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) refl (ApplyB .M) (ApplyB .M) (ApplyB .M) IdentB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) refl (ApplyB .M) (FunctorB .M) (FunctorB .M) (ApplyB .M) m f g = refl
    lawAssoc {β = β} {γ = γ} (inj₁ IdentTC) (inj₂ N) (inj₂ P) refl (ApplyB ._) b₂ b₃ (ApplyB .N) m f g = begin
      SuperMonad.bind SM b₂ (f m) g
        ≡⟨ {!!} ⟩
      SuperMonad.bind SM b₃ (f m) g ∎
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) refl (FunctorB .M) IdentB (FunctorB .M) (FunctorB .M) m f g 
      = cong (λ X → X m) (Functor.lawDist (SuperMonad.functor SM M) g f)
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ P) refl b₁ (ApplyB .P) b₃ (FunctorB .M) m f g = begin
      SuperMonad.bind SM b₁ m (g ∘ f)
        ≡⟨ {!!} ⟩
      SuperMonad.bind SM b₃ (fmap⟨ inj₂ M ⟩ f m) g ∎
    lawAssoc (inj₂ M) (inj₂ N) (inj₁ IdentTC) refl b₁ (FunctorB .N) (FunctorB ._) b₄ m f g = begin
      SuperMonad.bind SM b₁ m (λ x → fmap⟨ inj₂ N ⟩ g (f x)) 
        ≡⟨ {!!} ⟩
      fmap⟨ inj₂ (M ◆⟨ SM ⟩ N) ⟩ g (SuperMonad.bind SM b₄ m f) ∎
    lawAssoc {γ = γ} (inj₂ M) (inj₂ N) (inj₂ P) assoc b₁ b₂ b₃ b₄ m f g = begin
      subst (λ X → ⟨ X ⟩ γ) assoc (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))
        ≡⟨ sym (helper3 (M ◆⟨ SM ⟩ (N ◆⟨ SM ⟩ P)) ((M ◆⟨ SM ⟩ N) ◆⟨ SM ⟩ P) assoc (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))) ⟩ 
      subst (λ X → K⟨ SM ▷ X ⟩ γ) (helper1 assoc) (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))
        ≡⟨ SuperMonad.lawAssoc SM M N P (helper1 assoc) b₁ b₂ b₃ b₄ m f g ⟩ 
      SuperMonad.bind SM b₃ (SuperMonad.bind SM b₄ m f) g ∎
 
