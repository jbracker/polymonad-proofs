
module SuperMonad.MaybeListMonad where

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
open import Functor
open import Applicative
open import Monad
open import Monad.Maybe
open import Monad.List
open import Monad.Polymonad
open import SuperMonad.Definition 
open import SuperMonad.Monad
open import SuperMonad.HaskSuperMonad

-- This has natural and clear semantics
bindMaybeListList : [ Maybe , List ]▷ List
bindMaybeListList (Just x) f = f x
bindMaybeListList Nothing  f = Nil

-- These semantics are questionable...
-- Filter version:
-- This version may be closer to actual list semantics, since there an 
-- empty result of 'f' also leads to that element being removed.
bindListMaybeListFilter : [ List , Maybe ]▷ List
bindListMaybeListFilter (x ∷ xs) f with f x
bindListMaybeListFilter (x ∷ xs) f | Just y  = y ∷ bindListMaybeListFilter xs f -- This is clear
bindListMaybeListFilter (x ∷ xs) f | Nothing = bindListMaybeListFilter xs f -- Here we have a choice: Filter or Abort
bindListMaybeListFilter Nil f = Nil -- This is clear

-- Abort version:
bindListMaybeListAbort : [ List , Maybe ]▷ List
bindListMaybeListAbort (x ∷ xs) f with f x 
bindListMaybeListAbort (x ∷ xs) f | Just y  = y ∷ bindListMaybeListAbort xs f -- This is clear
bindListMaybeListAbort (x ∷ xs) f | Nothing = Nil -- Here we have a choice: Filter or Abort
                       -- Which kind of abort do we want to use? Do we return the part that 
                       -- was successful so far or an empty list of one of the elements maps 
                       -- to nothing?
bindListMaybeListAbort Nil f = Nil -- This is clear

data MaybeListBinds : Set where
  MaybeListBind : MaybeListBinds

MaybeListSuperMonad : SuperMonad (MonadTyCons ⊎ MonadTyCons)
MaybeListSuperMonad = record
  { ⟨_⟩ = ⟨_⟩
  ; Binds = Binds
  ; Returns = Returns
  ; functor = functor
  ; _◆_ = _◆_
  ; bind = bind
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
  } where
    TyCons = MonadTyCons ⊎ MonadTyCons

    MaybeTC : TyCons
    MaybeTC = inj₁ MonadTC

    ListTC : TyCons
    ListTC = inj₂ MonadTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ MonadTC) = Maybe
    ⟨_⟩ (inj₂ MonadTC) = List
    
    Binds : TyCons → TyCons → Set
    Binds (inj₁ MonadTC) (inj₁ MonadTC) = ⊤
    Binds (inj₁ MonadTC) (inj₂ MonadTC) = ⊤
    Binds (inj₂ MonadTC) (inj₁ MonadTC) = ⊥
    Binds (inj₂ MonadTC) (inj₂ MonadTC) = ⊤
    
    Returns : TyCons → Set
    Returns M = ⊤

    _◆_ : TyCons → TyCons → TyCons
    inj₁ MonadTC ◆ inj₁ MonadTC = MaybeTC
    inj₁ MonadTC ◆ inj₂ MonadTC = ListTC
    inj₂ MonadTC ◆ inj₁ MonadTC = ListTC
    inj₂ MonadTC ◆ inj₂ MonadTC = ListTC
    
    _>>=L_ = Monad._>>=_ monadList
    returnL = Monad.return monadList

    _>>=M_ = Monad._>>=_ monadMaybe
    returnM = Monad.return monadMaybe

    bind : {M N : TyCons} → Binds M N → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ M ◆ N ⟩
    bind {M = inj₁ MonadTC} {N = inj₁ MonadTC} tt ma f = ma >>=M f
    bind {M = inj₁ MonadTC} {N = inj₂ MonadTC} tt ma f = bindMaybeListList ma f
    bind {M = inj₂ MonadTC} {N = inj₁ MonadTC} () ma f
    bind {M = inj₂ MonadTC} {N = inj₂ MonadTC} tt ma f = ma >>=L f
   
    return : ∀ {α : Type} → {M : TyCons} → Returns M → α → ⟨ M ⟩ α
    return {M = inj₁ MonadTC} tt = returnM
    return {M = inj₂ MonadTC} tt = returnL
   
    fmap⟨_⟩ : (M : TyCons) → ∀ {α β : Type} → (α → β) → ⟨ M ⟩ α → ⟨ M ⟩ β
    fmap⟨_⟩ (inj₁ MonadTC) f ma = ma >>=M (returnM ∘ f)
    fmap⟨_⟩ (inj₂ MonadTC) f ma = ma >>=L (returnL ∘ f)
   
    lawIdR : ∀ {α β : Type} 
           → (M N : TyCons)
           → (N◆M≡M : N ◆ M ≡ M )
           → (b : Binds N M) → (r : Returns N)
           → (a : α) → (k : α → ⟨ M ⟩ β)
           → subst (λ X → ⟨ X ⟩ β) N◆M≡M (bind {M = N} {N = M} b (return r a) k) ≡ k a
    lawIdR (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt a f = Monad.lawIdR monadMaybe a f
    lawIdR (inj₁ MonadTC) (inj₂ MonadTC) () () tt a f
    lawIdR (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt a f = refl
    lawIdR (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt a f = Monad.lawIdR monadList a f
   
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawIdL (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt m = Monad.lawIdL monadMaybe m
    lawIdL (inj₁ MonadTC) (inj₂ MonadTC) () tt tt m
    lawIdL (inj₂ MonadTC) (inj₁ MonadTC) refl () tt m
    lawIdL (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt m = Monad.lawIdL monadList m
    
    lawAssoc : ∀ {α β γ : Type} 
             → (M N P : TyCons)
             → (assoc : M ◆ (N ◆ P) ≡ (M ◆ N) ◆ P) 
             → (b₁ : Binds M (N ◆ P)) → (b₂ : Binds N P)
             → (b₃ : Binds (M ◆ N) P) → (b₄ : Binds M N)
             → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → ⟨ P ⟩ γ)
             → subst (λ X → ⟨ X ⟩ γ) assoc (bind b₁ m (λ x → bind b₂ (f x) g)) 
               ≡ bind b₃ (bind b₄ m f) g
    lawAssoc (inj₁ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt m f g = Monad.lawAssoc monadMaybe m f g
    lawAssoc (inj₁ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (Just x) f g = refl
    lawAssoc (inj₁ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt Nothing  f g = refl
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt () () tt m f g
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (Just x) f g = refl
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt Nothing  f g = refl
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl () tt () () m f g
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt () m f g
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt () () tt m f g
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt m f g = Monad.lawAssoc monadList m f g -- Monad.lawAssoc monad m f g
    
    functor : (M : TyCons) → Functor ⟨ M ⟩
    functor (inj₁ MonadTC) = Applicative.functor (Monad.applicative monadMaybe)
    functor (inj₂ MonadTC) = Applicative.functor (Monad.applicative monadList)
    
    lawMonadFmap : ∀ {α β : Type}
                 → (M N : TyCons)
                 → (M◆N≡M : M ◆ N ≡ M)
                 → (b : Binds M N) → (r : Returns N)
                 → (f : α → β) → (m : ⟨ M ⟩ α)
                 → subst (λ X → ⟨ X ⟩ β) M◆N≡M (bind b m (return r ∘ f)) 
                   ≡ Functor.fmap (functor M) f m
    lawMonadFmap (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt f m = refl
    lawMonadFmap (inj₁ MonadTC) (inj₂ MonadTC) ()   tt tt f m
    lawMonadFmap (inj₂ MonadTC) (inj₁ MonadTC) refl () tt f m
    lawMonadFmap (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt f m = refl

MaybeListHaskSuperMonad : HaskSuperMonad (MonadTyCons ⊎ MonadTyCons)
MaybeListHaskSuperMonad  = record
  { supermonad = supermonad
  ; lawUniqueBind = lawUniqueBind
  ; lawCommuteFmapBind = lawCommuteFmapBind
  ; lawDecomposeFmapIntro = lawDecomposeFmapIntro
  } where
    supermonad : SuperMonad (MonadTyCons ⊎ MonadTyCons)
    supermonad = MaybeListSuperMonad
    
    TyCons = MonadTyCons ⊎ MonadTyCons
    Binds = SuperMonad.Binds supermonad
    ⟨_⟩ = SuperMonad.⟨_⟩ supermonad
    bind = SuperMonad.bind supermonad
    functor = SuperMonad.functor supermonad
    _◆_ = SuperMonad._◆_ supermonad
    
    _>>=L_ = Monad._>>=_ monadList
    returnL = Monad.return monadList

    _>>=M_ = Monad._>>=_ monadMaybe
    returnM = Monad.return monadMaybe

    _>>=MLL_ = bindMaybeListList
    
    open Functor.Functor
    
    lawUniqueBind : {α β : Type}
                  → (M N : TyCons)
                  → (b₁ b₂ : Binds M N)
                  → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β)
                  → bind b₁ m f ≡ bind b₂ m f
    lawUniqueBind (inj₁ MonadTC) (inj₁ MonadTC) tt tt m f = refl
    lawUniqueBind (inj₁ MonadTC) (inj₂ MonadTC) tt tt m f = refl
    lawUniqueBind (inj₂ MonadTC) (inj₁ MonadTC) () () m f
    lawUniqueBind (inj₂ MonadTC) (inj₂ MonadTC) tt tt m f = refl
    
    lawCommuteFmapBind : {α β γ : Type} 
                       → (M N : TyCons)
                       → (b : Binds M N)
                       → (m : ⟨ M ⟩ α) → (f : α → ⟨ N ⟩ β) → (g : β → γ)
                       → fmap (functor (M ◆ N)) g (bind b m f) ≡ bind b m (λ x → fmap (functor N) g (f x))
    lawCommuteFmapBind (inj₁ MonadTC) (inj₁ MonadTC) tt m f g 
      = HaskSuperMonad.lawCommuteFmapBind (Monad→HaskSuperMonad Maybe monadMaybe) MonadTC MonadTC tt m f g
    lawCommuteFmapBind (inj₁ MonadTC) (inj₂ MonadTC) tt m f g 
      = sym (SuperMonad.lawAssoc supermonad (inj₁ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt m f (returnL ∘ g))
    lawCommuteFmapBind (inj₂ MonadTC) (inj₁ MonadTC) () m f g
    lawCommuteFmapBind (inj₂ MonadTC) (inj₂ MonadTC) tt m f g 
      = HaskSuperMonad.lawCommuteFmapBind (Monad→HaskSuperMonad List monadList) MonadTC MonadTC tt m f g
    
    lawDecomposeFmapIntro : {α β γ : Type} 
                          → (M N : TyCons)
                          → (b : Binds M N)
                          → (m : ⟨ M ⟩ α) → (f : α → β) → (g : β → ⟨ N ⟩ γ)
                          → bind b m (g ∘ f) ≡ bind b (fmap (functor M) f m) g
    lawDecomposeFmapIntro (inj₁ MonadTC) (inj₁ MonadTC) tt m f g 
      = HaskSuperMonad.lawDecomposeFmapIntro (Monad→HaskSuperMonad Maybe monadMaybe) MonadTC MonadTC tt m f g
    lawDecomposeFmapIntro (inj₁ MonadTC) (inj₂ MonadTC) tt m f g = begin
      m >>=MLL (g ∘ f)
        ≡⟨ cong (λ X → m >>=MLL X) (funExt (λ x → sym (SuperMonad.lawIdR supermonad (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt (f x) g))) ⟩
      m >>=MLL (λ x → returnM (f x) >>=MLL g) 
        ≡⟨ SuperMonad.lawAssoc supermonad (inj₁ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt m (returnM ∘ f) g ⟩
      (m >>=M (returnM ∘ f)) >>=MLL g ∎
    lawDecomposeFmapIntro (inj₂ MonadTC) (inj₁ MonadTC) () m f g
    lawDecomposeFmapIntro (inj₂ MonadTC) (inj₂ MonadTC) tt m f g 
      = HaskSuperMonad.lawDecomposeFmapIntro (Monad→HaskSuperMonad List monadList) MonadTC MonadTC tt m f g
