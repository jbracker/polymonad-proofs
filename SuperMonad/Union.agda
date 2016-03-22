
module SuperMonad.Union where

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
open import SuperMonad.HaskSuperMonad
{-
LiftedSuperMonad : ∀ {ℓ₁ ℓ₂} {TyCons : Set ℓ₁} 
                 → SuperMonad {ℓ = ℓ₁} TyCons → SuperMonad (Lift {ℓ = ℓ₁ ⊔ ℓ₂} TyCons)
LiftedSuperMonad {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {TyCons = TCs} sm = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = bind
  ; return = return
  ; lawIdR = {!!}
  ; lawIdL = {!!}
  ; lawAssoc = {!!}
  ; lawMonadFmap = {!!}
  } where
    ℓ = ℓ₁ ⊔ ℓ₂
    
    TyCons = Lift {ℓ = ℓ} TCs
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (lift M) = K⟨ sm ▷ M ⟩
    
    Binds : TyCons → TyCons → Set ℓ
    Binds (lift M) (lift N) = Lift {ℓ = ℓ} (SuperMonad.Binds sm M N)
    
    Returns : TyCons → Set ℓ
    Returns (lift M) = Lift {ℓ = ℓ} (SuperMonad.Returns sm M)
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (lift M) = SuperMonad.functor sm M
    
    _◆_ : TyCons → TyCons → TyCons
    lift M ◆ lift N = lift {ℓ = ℓ} (SuperMonad._◆_ sm M N)
    
    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind (lift b) = SuperMonad.bind sm b
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return (lift r) = SuperMonad.return sm r
   
    lowerEq : {N M : TCs} → _≡_ {ℓ} {TyCons} (lift {ℓ = ℓ} N) (lift {ℓ = ℓ} M) → _≡_ {ℓ₁} {TCs} N M
    lowerEq refl = refl
    
    lowerEq' : {N M : TCs} 
             → lift {ℓ = ℓ} M ◆ lift {ℓ = ℓ} N ≡ lift {ℓ = ℓ} M 
             → lift {ℓ = ℓ} (SuperMonad._◆_  sm M N) ≡ lift {ℓ = ℓ} M
    lowerEq' eq = eq

    lowerEq'' : {N M : TCs} 
              → lift {ℓ = ℓ} M ◆ lift {ℓ = ℓ} N ≡ lift {ℓ = ℓ} (SuperMonad._◆_ sm M N)
    lowerEq'' = refl

    lowerB : ∀ {M N : TCs} → Binds (lift M) (lift N) → SuperMonad.Binds sm M N
    lowerB (lift b) = b
    lowerR : ∀ {M : TCs} → Returns (lift M) → SuperMonad.Returns sm M
    lowerR (lift r) = r
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind {M = M} {N = N} b {α = α} {β = α} m (return {M = N} r)) ≡ m
    lawIdL (lift M) (lift N) M◆N≡M (lift b) (lift r) m = SuperMonad.lawIdL sm M N (lowerEq (lowerEq' {!M◆N≡M!})) b r m

    lawIdL' : ∀ {α : Type} 
           → (M N : TCs)
           → (M◆N≡M : lift M ◆ lift N ≡ lift M)
           → (b : Binds (lift M) (lift N)) → (r : Returns (lift N))
           → (m : ⟨ lift M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (SuperMonad.bind sm {M = M} {N = N} (lowerB b) {α = α} {β = α} m (SuperMonad.return sm {M = N} (lowerR r))) ≡ m
    lawIdL' M N M◆N≡M (lift b) (lift r) m = SuperMonad.lawIdL sm M N (lowerEq {!M◆N≡M!}) b r m
    -}
    
superMonadUnion : ∀ {ℓ} {TyCons₁ : Set ℓ} {TyCons₂ : Set ℓ}
                → SuperMonad TyCons₁
                → SuperMonad TyCons₂
                → SuperMonad (TyCons₁ ⊎ TyCons₂)
superMonadUnion {ℓ = ℓ} {TyCons₁ = TyCons₁} {TyCons₂ = TyCons₂} monad₁ monad₂ = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = λ {M} {N} → bind {M} {N}
  ; return = λ {α} {M} → return {α} {M}
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where 
    TyCons = TyCons₁ ⊎ TyCons₂
    
    _◆₁_ = SuperMonad._◆_ monad₁
    _◆₂_ = SuperMonad._◆_ monad₂
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ M₁) = K⟨ monad₁ ▷ M₁ ⟩
    ⟨_⟩ (inj₂ M₂) = K⟨ monad₂ ▷ M₂ ⟩
    
    Binds : TyCons → TyCons → Set ℓ
    Binds (inj₁ M₁) (inj₁ N₁) = (SuperMonad.Binds monad₁ M₁ N₁)
    Binds (inj₁ M₁) (inj₂ N₂) = Lift ⊥
    Binds (inj₂ M₂) (inj₁ N₁) = Lift ⊥
    Binds (inj₂ M₂) (inj₂ N₂) = (SuperMonad.Binds monad₂ M₂ N₂)
    
    Returns : TyCons → Set ℓ
    Returns (inj₁ M₁) = (SuperMonad.Returns monad₁ M₁)
    Returns (inj₂ M₂) = (SuperMonad.Returns monad₂ M₂)

    _◆_ : TyCons → TyCons → TyCons
    inj₁ M₁ ◆ inj₁ N₁ = inj₁ (SuperMonad._◆_ monad₁ M₁ N₁)
    inj₁ M₁ ◆ inj₂ N₂ = inj₁ M₁ -- Never happens: No binds for this
    inj₂ M₂ ◆ inj₁ N₁ = inj₂ M₂ -- Never happens: No binds for this
    inj₂ M₂ ◆ inj₂ N₂ = inj₂ (SuperMonad._◆_ monad₂ M₂ N₂)

    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {inj₁ M₁} {inj₁ N₁} b ma f = SuperMonad.bind monad₁ b ma f
    bind {inj₁ M₁} {inj₂ N₂} (lift ()) ma f
    bind {inj₂ M₂} {inj₁ N₁} (lift ()) ma f
    bind {inj₂ M₂} {inj₂ N₂} b ma f = SuperMonad.bind monad₂ b ma f
    
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = inj₁ M₁} b x = SuperMonad.return monad₁ b x
    return {M = inj₂ M₂} b x = SuperMonad.return monad₂ b x
    
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (inj₁ M₁) f ma = Functor.fmap (SuperMonad.functor monad₁ M₁) f ma
    fmap⟨_⟩ (inj₂ M₂) f ma = Functor.fmap (SuperMonad.functor monad₂ M₂) f ma
    
    lowerEq₁ : {N M : TyCons₁} → inj₁ {B = TyCons₂} N ≡ inj₁ M → N ≡ M
    lowerEq₁ refl = refl
    
    lowerEq₂ : {N M : TyCons₂} → inj₂ {A = TyCons₁} N ≡ inj₂ M → N ≡ M
    lowerEq₂ refl = refl
    
    embedProof₁ : {α : Type} {M N : TyCons₁} (eq : inj₁ M ≡ inj₁ N) 
                → {x : ⟨ inj₁ M ⟩ α} → {y : ⟨ inj₁ N ⟩ α} 
                → subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (lowerEq₁ eq) x ≡ y 
                → subst (λ X → ⟨ X ⟩ α) eq x ≡ y
    embedProof₁ {α = α} eq {x = x} {y = y} proof = begin
      subst (λ X → ⟨ X ⟩ α) eq x
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) eq X) 
                (sym (subst²≡id' (lowerEq₁ eq) (λ X → K⟨ monad₁ ▷ X ⟩ α) x)) ⟩
      subst (λ X → ⟨ X ⟩ α) eq
            (subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (sym (lowerEq₁ eq)) 
                   (subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (lowerEq₁ eq) x ) )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (sym (lowerEq₁ eq)) X)) proof ⟩
      subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (sym (lowerEq₁ eq)) y )
        ≡⟨ substHelper1 eq y ⟩
      y ∎ 
      where
        substHelper1 : {α : Type} {M N : TyCons₁}
                     → (eq : inj₁ M ≡ inj₁ N)
                     → (x : ⟨ inj₁ N ⟩ α)
                     → subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₁ ▷ X ⟩ α) (sym (lowerEq₁ eq)) x) ≡ x
        substHelper1 refl x = refl
    
    embedProof₂ : {α : Type} {M N : TyCons₂} (eq : inj₂ M ≡ inj₂ N) 
                → {x : ⟨ inj₂ M ⟩ α} → {y : ⟨ inj₂ N ⟩ α} 
                → subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (lowerEq₂ eq) x ≡ y 
                → subst (λ X → ⟨ X ⟩ α) eq x ≡ y
    embedProof₂ {α = α} eq {x = x} {y = y} proof = begin
      subst (λ X → ⟨ X ⟩ α) eq x
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) eq X) 
                (sym (subst²≡id' (lowerEq₂ eq) (λ X → K⟨ monad₂ ▷ X ⟩ α) x)) ⟩
      subst (λ X → ⟨ X ⟩ α) eq
            (subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (sym (lowerEq₂ eq)) 
                   (subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (lowerEq₂ eq) x ) )
        ≡⟨ cong (λ X → subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (sym (lowerEq₂ eq)) X)) proof ⟩
      subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (sym (lowerEq₂ eq)) y )
        ≡⟨ substHelper2 eq y ⟩
      y ∎
      where
        substHelper2 : {α : Type} {M N : TyCons₂}
                     → (eq : inj₂ M ≡ inj₂ N)
                     → (x : ⟨ inj₂ N ⟩ α)
                     → subst (λ X → ⟨ X ⟩ α) eq (subst (λ X → K⟨ monad₂ ▷ X ⟩ α) (sym (lowerEq₂ eq)) x) ≡ x
        substHelper2 refl x = refl
    
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind {M = N} {N = M} b {α = α} {β = β} (return {M = N} r a) k) ≡ k a
    lawIdR {α = α} {β = β} (inj₁ M₁) (inj₁ N₁) N◆M≡M b r a f 
      = embedProof₁ N◆M≡M (SuperMonad.lawIdR monad₁ M₁ N₁ (lowerEq₁ N◆M≡M) b r a f)
    lawIdR (inj₁ M₁) (inj₂ N₂) N◆M≡M (lift ()) r a f
    lawIdR (inj₂ M₂) (inj₁ N₁) N◆M≡M (lift ()) r a f
    lawIdR {α = α} {β = β} (inj₂ M₂) (inj₂ N₂) N◆M≡M b r a f 
      = embedProof₂ N◆M≡M (SuperMonad.lawIdR monad₂ M₂ N₂ (lowerEq₂ N◆M≡M) b r a f)
    
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind {M = M} {N = N} b {α = α} {β = α} m (return {M = N} r)) ≡ m
    lawIdL {α = α} (inj₁ M₁) (inj₁ N₁) M◆N≡M b r m 
      = embedProof₁ M◆N≡M (SuperMonad.lawIdL monad₁ M₁ N₁ (lowerEq₁ M◆N≡M) b r m)
    lawIdL (inj₁ M₁) (inj₂ N₂) M◆N≡M (lift ()) r m
    lawIdL (inj₂ M₂) (inj₁ N₁) M◆N≡M (lift ()) r m
    lawIdL {α = α} (inj₂ M₂) (inj₂ N₂) M◆N≡M b r m 
      = embedProof₂ M◆N≡M (SuperMonad.lawIdL monad₂ M₂ N₂ (lowerEq₂ M◆N≡M) b r m)
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind {M = M} {N = N ◆ P} b₁ {α = α} {β = γ} m (λ x → bind {M = N} {N = P} b₂ {α = β} {β = γ} (f x) g)) 
               ≡ bind {M = M ◆ N} {N = P} b₃ {α = β} {β = γ} (bind {M = M} {N = N} b₄ {α = α} {β = β} m f) g
    lawAssoc {γ = γ} (inj₁ M₁) (inj₁ N₁) (inj₁ P₁) assoc b₁ b₂ b₃ b₄ m f g 
      = embedProof₁ assoc (SuperMonad.lawAssoc monad₁ M₁ N₁ P₁ (lowerEq₁ assoc) b₁ b₂ b₃ b₄ m f g)
    lawAssoc (inj₁ M₁) (inj₁ N₁) (inj₂ P₂) assoc b₁ (lift ()) (lift ()) b₄ m f g
    lawAssoc (inj₁ M₁) (inj₂ N₂) (inj₁ P₁) assoc (lift ()) (lift ()) b₃ (lift ()) m f g
    lawAssoc (inj₁ M₁) (inj₂ N₂) (inj₂ P₂) assoc (lift ()) b₂ (lift ()) (lift ()) m f g
    lawAssoc (inj₂ M₂) (inj₁ N₁) (inj₁ P₁) assoc (lift ()) b₂ (lift ()) (lift ()) m f g
    lawAssoc (inj₂ M₂) (inj₁ N₁) (inj₂ P₂) assoc (lift ()) (lift ()) b₃ (lift ()) m f g
    lawAssoc (inj₂ M₂) (inj₂ N₂) (inj₁ P₁) assoc b₁ (lift ()) (lift ()) b₄ m f g
    lawAssoc {γ = γ} (inj₂ M₂) (inj₂ N₂) (inj₂ P₂) assoc b₁ b₂ b₃ b₄ m f g 
      = embedProof₂ assoc (SuperMonad.lawAssoc monad₂ M₂ N₂ P₂ (lowerEq₂ assoc) b₁ b₂ b₃ b₄ m f g)
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (inj₁ M₁) = SuperMonad.functor monad₁ M₁
    functor (inj₂ M₂) = SuperMonad.functor monad₂ M₂
      
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (M◆N≡M : M ◆ N ≡ M)
                 → (b : Binds M N) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → subst (λ X → ⟨ X ⟩ β) M◆N≡M (bind {M = M} {N = N} b {α = α} {β = β} m (return {M = N} r ∘ f)) 
                   ≡ Functor.fmap (functor M) f m
    lawMonadFmap {β = β} (inj₁ M₁) (inj₁ N₁) M◆N≡M b r f m 
      = embedProof₁ M◆N≡M (SuperMonad.lawMonadFmap monad₁ M₁ N₁ (lowerEq₁ M◆N≡M) b r f m)
    lawMonadFmap (inj₁ M₁) (inj₂ N₂) M◆N≡M (lift ()) r f m
    lawMonadFmap (inj₂ M₂) (inj₁ N₁) M◆N≡M (lift ()) r f m
    lawMonadFmap (inj₂ M₂) (inj₂ N₂) M◆N≡M b r f m 
      = embedProof₂ M◆N≡M (SuperMonad.lawMonadFmap monad₂ M₂ N₂ (lowerEq₂ M◆N≡M) b r f m)



haskSuperMonadUnion : ∀ {ℓ} {TyCons₁ : Set ℓ} {TyCons₂ : Set ℓ}
                    → HaskSuperMonad TyCons₁
                    → HaskSuperMonad TyCons₂
                    → HaskSuperMonad (TyCons₁ ⊎ TyCons₂)
haskSuperMonadUnion {TyCons₁ = TyCons₁} {TyCons₂ = TyCons₂} haskMonad₁ haskMonad₂ = record
  { supermonad = supermonad
  ; lawUniqueBind = lawUniqueBind
  ; lawCommuteFmapBind = lawCommuteFmapBind
  ; lawDecomposeFmapIntro = lawDecomposeFmapIntro
  } where
    TyCons = TyCons₁ ⊎ TyCons₂
    
    monad₁ = HaskSuperMonad.supermonad haskMonad₁
    monad₂ = HaskSuperMonad.supermonad haskMonad₂
    
    supermonad : SuperMonad TyCons
    supermonad = superMonadUnion monad₁ monad₂
    
    ⟨_⟩ = SuperMonad.⟨_⟩ supermonad
    _◆_ = SuperMonad._◆_ supermonad
    Binds = SuperMonad.Binds supermonad
    bind = SuperMonad.bind supermonad
    functor = SuperMonad.functor supermonad
    fmap = Functor.fmap

    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind {M = M} {N = N} b₁ m f ≡ bind {M = M} {N = N} b₂ m f
    lawUniqueBind (inj₁ M₁) (inj₁ N₁) b₁ b₂ m f 
      = HaskSuperMonad.lawUniqueBind haskMonad₁ M₁ N₁ b₁ b₂ m f
    lawUniqueBind (inj₁ M₁) (inj₂ N₂) (lift ()) (lift ()) m f
    lawUniqueBind (inj₂ M₂) (inj₁ N₁) (lift ()) (lift ()) m f
    lawUniqueBind (inj₂ M₂) (inj₂ N₂) b₁ b₂ m f 
      = HaskSuperMonad.lawUniqueBind haskMonad₂ M₂ N₂ b₁ b₂ m f
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → fmap (functor (M ◆ N)) g (bind {M = M} {N = N} b m f) ≡ bind {M = M} {N = N} b m (λ x → fmap (functor N) g (f x))
    lawCommuteFmapBind (inj₁ M₁) (inj₁ N₁) b m f g 
      = HaskSuperMonad.lawCommuteFmapBind haskMonad₁ M₁ N₁ b m f g
    lawCommuteFmapBind (inj₁ M₁) (inj₂ N₂) (lift ()) m f g
    lawCommuteFmapBind (inj₂ M₂) (inj₁ N₁) (lift ()) m f g
    lawCommuteFmapBind (inj₂ M₂) (inj₂ N₂) b m f g 
      = HaskSuperMonad.lawCommuteFmapBind haskMonad₂ M₂ N₂ b m f g
    
    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind {M = M} {N = N} b m (g ∘ f) ≡ bind {M = M} {N = N} b (fmap (functor M) f m) g
    lawDecomposeFmapIntro (inj₁ M₁) (inj₁ N₁) b m f g 
      = HaskSuperMonad.lawDecomposeFmapIntro haskMonad₁ M₁ N₁ b m f g
    lawDecomposeFmapIntro (inj₁ M₁) (inj₂ N₂) (lift ()) m f g
    lawDecomposeFmapIntro (inj₂ M₂) (inj₁ N₁) (lift ()) m f g
    lawDecomposeFmapIntro (inj₂ M₂) (inj₂ N₂) b m f g 
      = HaskSuperMonad.lawDecomposeFmapIntro haskMonad₂ M₂ N₂ b m f g
