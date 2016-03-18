
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

-- -----------------------------------------------------------------------------
-- Second version that uses the unclear [ List , Maybe ]▷ List version as well.

data MaybeListBindsFilter : TyCon → TyCon → Set where
  MaybeListListBind : MaybeListBindsFilter Maybe List
  ListMaybeListBind : MaybeListBindsFilter List Maybe

MaybeListSuperMonadFilter : SuperMonad (MonadTyCons ⊎ MonadTyCons)
MaybeListSuperMonadFilter = record
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
    Binds (inj₂ MonadTC) (inj₁ MonadTC) = ⊤
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
    bind {M = inj₂ MonadTC} {N = inj₁ MonadTC} tt ma f = bindListMaybeListFilter ma f
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
    lawIdR (inj₁ MonadTC) (inj₂ MonadTC) ()   tt tt a f
    lawIdR (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt a f = refl
    lawIdR (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt a f = Monad.lawIdR monadList a f
   
    lawIdL : ∀ {α : Type} 
           → (M N : TyCons)
           → (M◆N≡M : M ◆ N ≡ M)
           → (b : Binds M N) → (r : Returns N)
           → (m : ⟨ M ⟩ α)
           → subst (λ X → ⟨ X ⟩ α) M◆N≡M (bind b m (return r)) ≡ m
    lawIdL (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt m = Monad.lawIdL monadMaybe m
    lawIdL (inj₁ MonadTC) (inj₂ MonadTC) ()   tt tt m
    lawIdL (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt (x ∷ xs) = cong (λ XS → x ∷ XS) (lawIdL ListTC MaybeTC refl tt tt xs)
    lawIdL (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt Nil      = refl
    lawIdL (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt m = Monad.lawIdL monadList m
    
    lawAssocHelp : ∀ {α β γ : Type}
                 → (xs : List α) (ys : List β) (f : α → List β) (g : β → Maybe γ)
                 → bindListMaybeListFilter ys g ++ bindList xs (λ y → bindListMaybeListFilter (f y) g)
                 ≡ bindListMaybeListFilter (ys ++ bindList xs f) g
    lawAssocHelp xs (y ∷ ys) f g with g y
    lawAssocHelp xs (y ∷ ys) f g | Just x = cong (λ XS → x ∷ XS) (lawAssocHelp xs ys f g)
    lawAssocHelp xs (y ∷ ys) f g | Nothing = lawAssocHelp xs ys f g
    lawAssocHelp (x ∷ xs) Nil f g = lawAssocHelp xs (f x) f g
    lawAssocHelp Nil Nil f g = refl
    
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
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (Just x) f g = refl
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt Nothing  f g = refl
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (Just x) f g = refl
    lawAssoc (inj₁ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt tt tt Nothing  f g = refl
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g with f x
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Just y with g y
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Just y | Just z
      = cong (λ ZS → z ∷ ZS) (lawAssoc ListTC MaybeTC MaybeTC refl tt tt tt tt xs f g)
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Just y | Nothing
      = lawAssoc ListTC MaybeTC MaybeTC refl tt tt tt tt xs f g
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Nothing 
      = lawAssoc ListTC MaybeTC MaybeTC refl tt tt tt tt xs f g
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₁ MonadTC) refl tt tt tt tt Nil      f g = refl
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (x ∷ xs) f g with f x
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Just y 
      = cong (λ X → g y ++ X) (lawAssoc ListTC MaybeTC ListTC refl tt tt tt tt xs f g)
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Nothing 
      = lawAssoc ListTC MaybeTC ListTC refl tt tt tt tt xs f g
    lawAssoc (inj₂ MonadTC) (inj₁ MonadTC) (inj₂ MonadTC) refl tt tt tt tt Nil      f g = refl
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g with f x
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | y ∷ ys with g y
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | y ∷ ys | Just z
      = cong (λ ZS → z ∷ ZS) (lawAssocHelp xs ys f g)
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | y ∷ ys | Nothing 
      = lawAssocHelp xs ys f g
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt (x ∷ xs) f g | Nil 
      = lawAssoc ListTC ListTC MaybeTC refl tt tt tt tt xs f g
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt tt tt Nil      f g = refl
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
    lawMonadFmap {α = α} (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt f (x ∷ xs)
      = cong (λ X → f x ∷ X) (lawMonadFmap {α = α} ListTC MaybeTC refl tt tt f xs)
    lawMonadFmap (inj₂ MonadTC) (inj₁ MonadTC) refl tt tt f Nil = refl
    lawMonadFmap (inj₂ MonadTC) (inj₂ MonadTC) refl tt tt f m = refl
