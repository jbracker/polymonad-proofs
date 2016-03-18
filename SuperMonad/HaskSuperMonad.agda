
module SuperMonad.HaskSuperMonad where

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


record HaskSuperMonad {ℓ} (TyCons : Set ℓ) : Set (lsuc ℓ) where
  open SuperMonad {{...}}
  open Functor.Functor
  field
    supermonad : SuperMonad TyCons
    
    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind b₁ m f ≡ bind b₂ m f
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → fmap (functor (M ◆ N)) g (bind b m f) ≡ bind b m (λ x → fmap (functor N) g (f x))
    
    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind b m (g ∘ f) ≡ bind b (fmap (functor M) f m) g

data IdReturns {ℓ} : Set ℓ where
  IdentR : IdReturns

data FunctorBinds {ℓ} {TyCons : Set ℓ} : (IdTyCons ⊎ TyCons) → (IdTyCons ⊎ TyCons) → Set ℓ where
  FunctorB : (M : TyCons) → FunctorBinds (inj₂ M) idTC
  ApplyB   : (M : TyCons) → FunctorBinds idTC (inj₂ M)

extendHaskSuperMonadWithFunctorBind : ∀ {ℓ} {TyCons : Set ℓ} 
                                    → HaskSuperMonad TyCons
                                    → HaskSuperMonad (IdTyCons ⊎ TyCons)
extendHaskSuperMonadWithFunctorBind {ℓ = ℓ} {TyCons = TCs} HSM = record
  { supermonad = record
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
    ; lawMonadFmap = lawMonadFmap
    }
  ; lawUniqueBind = lawUniqueBind
  ; lawCommuteFmapBind = lawCommuteFmapBind
  ; lawDecomposeFmapIntro = lawDecomposeFmapIntro
  } where
    TyCons = IdTyCons ⊎ TCs

    SM = HaskSuperMonad.supermonad HSM
    
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
    
    helper3 : {α : Type} 
            → (M N : TCs)
            → (M≡N : inj₂ M ≡ inj₂ N)
            → (x : ⟨ inj₂ M ⟩ α)
            → subst (λ X → K⟨ SM ▷ X ⟩ α) (helper1 M≡N) x ≡ subst (λ X → ⟨ X ⟩ α) M≡N x
    helper3 M .M refl x = refl
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (M◆N≡M : M ◆ N ≡ M)
                 → (b : Binds M N) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → subst (λ X → ⟨ X ⟩ β) M◆N≡M (bind {M = M} {N = N} b m (return {M = N} r ∘ f)) 
                   ≡ Functor.fmap (functor M) f m
    lawMonadFmap (inj₁ IdentTC) (inj₁ IdentTC) refl IdentB IdentR f m = refl
    lawMonadFmap (inj₁ IdentTC) (inj₂ M) () (ApplyB .M) r f m
    lawMonadFmap (inj₂ M) (inj₁ IdentTC) refl (FunctorB .M) IdentR f m = refl
    lawMonadFmap {β = β} (inj₂ M) (inj₂ N) M◆N≡M b r f m = begin 
      subst (λ X → ⟨ X ⟩ β) M◆N≡M (SuperMonad.bind SM b m ((SuperMonad.return SM r) ∘ f))
        ≡⟨ sym (helper3 (M ◆⟨ SM ⟩ N) M M◆N≡M (SuperMonad.bind SM b m ((SuperMonad.return SM r) ∘ f))) ⟩ 
      subst (λ X → K⟨ SM ▷ X ⟩ β) (helper1 M◆N≡M) (SuperMonad.bind SM b m ((SuperMonad.return SM r) ∘ f))
        ≡⟨ SuperMonad.lawMonadFmap SM M N (helper1 M◆N≡M) b r f m ⟩
      Functor.fmap (SuperMonad.functor SM M) f m ∎
    
    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind {M = M} {N = N} b₁ m f ≡ bind {M = M} {N = N} b₂ m f
    lawUniqueBind (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB m f = refl
    lawUniqueBind (inj₁ IdentTC) (inj₂ M) (ApplyB .M) (ApplyB .M) m f = refl
    lawUniqueBind (inj₂ M) (inj₁ IdentTC) (FunctorB .M) (FunctorB .M) m f = refl
    lawUniqueBind (inj₂ M) (inj₂ N) b₁ b₂ m f = HaskSuperMonad.lawUniqueBind HSM M N b₁ b₂ m f
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → Functor.fmap (functor (M ◆ N)) g (bind {M = M} {N = N} b m f) 
                         ≡ bind {M = M} {N = N} b m (λ x → Functor.fmap (functor N) g (f x))
    lawCommuteFmapBind (inj₁ IdentTC) (inj₁ IdentTC) IdentB m f g = refl
    lawCommuteFmapBind (inj₁ IdentTC) (inj₂ M) (ApplyB .M) m f g = refl
    lawCommuteFmapBind (inj₂ M) (inj₁ IdentTC) (FunctorB .M) m f g 
      = cong (λ X → X m) (sym (Functor.lawDist (functor (inj₂ M)) g f))
    lawCommuteFmapBind (inj₂ M) (inj₂ N) b m f g 
      = HaskSuperMonad.lawCommuteFmapBind HSM M N b m f g
    
    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind {M = M} {N = N} b m (g ∘ f) 
                            ≡ bind {M = M} {N = N} b (Functor.fmap (functor M) f m) g
    lawDecomposeFmapIntro (inj₁ IdentTC) (inj₁ IdentTC) IdentB m f g = refl
    lawDecomposeFmapIntro (inj₁ IdentTC) (inj₂ M) (ApplyB .M) m f g = refl
    lawDecomposeFmapIntro (inj₂ M) (inj₁ IdentTC) (FunctorB .M) m f g
      = cong (λ X → X m) (Functor.lawDist (functor (inj₂ M)) g f)
    lawDecomposeFmapIntro (inj₂ M) (inj₂ N) b m f g
      = HaskSuperMonad.lawDecomposeFmapIntro HSM M N b m f g
    
    Id◆M≡M : ∀ {N} → idTC ◆ inj₂ N ≡ inj₂ N
    Id◆M≡M = refl
    
    M◆Id≡M : ∀ {N} → inj₂ N ◆ idTC ≡ inj₂ N
    M◆Id≡M = refl
    
    Id◆[N◆P]≡[Id◆N]◆P : ∀ {N P} → idTC ◆ (inj₂ N ◆ inj₂ P) ≡ (idTC ◆ inj₂ N) ◆ inj₂ P 
    Id◆[N◆P]≡[Id◆N]◆P = refl
    
    M◆[Id◆P]≡[M◆Id]◆P : ∀ {M P} → inj₂ M ◆ (idTC ◆ inj₂ P) ≡ (inj₂ M ◆ idTC) ◆ inj₂ P 
    M◆[Id◆P]≡[M◆Id]◆P = refl
    
    [M◆Id]◆P≡M◆P : ∀ {M P} → (inj₂ M ◆ idTC) ◆ inj₂ P ≡ inj₂ M ◆ inj₂ P 
    [M◆Id]◆P≡M◆P = refl
    
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
        ≡⟨ lawUniqueBind (inj₂ N) (inj₂ P) b₂ b₃ (f m) g ⟩
      SuperMonad.bind SM b₃ (f m) g ∎
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) refl (FunctorB .M) IdentB (FunctorB .M) (FunctorB .M) m f g 
      = cong (λ X → X m) (Functor.lawDist (SuperMonad.functor SM M) g f)
    lawAssoc {β = β} {γ = γ} (inj₂ M) (inj₁ IdentTC) (inj₂ P) refl b₁ (ApplyB .P) b₃ (FunctorB .M) m f g = begin
      SuperMonad.bind SM b₁ m (g ∘ f)
        ≡⟨ lawUniqueBind (inj₂ M) (inj₂ P) b₁ b₃ m (g ∘ f) ⟩
      SuperMonad.bind SM b₃ m (g ∘ f)
        ≡⟨ lawDecomposeFmapIntro (inj₂ M) (inj₂ P) b₃ m f g ⟩
      SuperMonad.bind SM b₃ (fmap⟨ inj₂ M ⟩ f m) g ∎
    lawAssoc {γ = γ} (inj₂ M) (inj₂ N) (inj₁ IdentTC) refl b₁ (FunctorB .N) (FunctorB ._) b₄ m f g = begin
      SuperMonad.bind SM b₁ m (λ x → fmap⟨ inj₂ N ⟩ g (f x)) 
        ≡⟨ lawUniqueBind (inj₂ M) (inj₂ N) b₁ b₄ m (λ x → fmap⟨ inj₂ N ⟩ g (f x)) ⟩
      SuperMonad.bind SM b₄ m (λ x → fmap⟨ inj₂ N ⟩ g (f x)) 
        ≡⟨ sym (lawCommuteFmapBind (inj₂ M) (inj₂ N) b₄ m f g) ⟩
      fmap⟨ inj₂ (M ◆⟨ SM ⟩ N) ⟩ g (SuperMonad.bind SM b₄ m f) ∎
    lawAssoc {γ = γ} (inj₂ M) (inj₂ N) (inj₂ P) assoc b₁ b₂ b₃ b₄ m f g = begin
      subst (λ X → ⟨ X ⟩ γ) assoc (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))
        ≡⟨ sym (helper3 (M ◆⟨ SM ⟩ (N ◆⟨ SM ⟩ P)) ((M ◆⟨ SM ⟩ N) ◆⟨ SM ⟩ P) assoc (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))) ⟩ 
      subst (λ X → K⟨ SM ▷ X ⟩ γ) (helper1 assoc) (SuperMonad.bind SM b₁ m (λ x → SuperMonad.bind SM b₂ (f x) g))
        ≡⟨ SuperMonad.lawAssoc SM M N P (helper1 assoc) b₁ b₂ b₃ b₄ m f g ⟩ 
      SuperMonad.bind SM b₃ (SuperMonad.bind SM b₄ m f) g ∎
 
