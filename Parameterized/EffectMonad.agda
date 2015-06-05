 
module Parameterized.EffectMonad where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.Identity

-- TODO: This is still unfinished work, since the constraints that can be applied to the monoid
-- elements are not modelled at all right now.

module Monoid where
  record Monoid {k} (C : Set k) : Set k where
    field
      ε : C
      _∙_ : C → C → C
    
      lawIdR : (m : C) → m ∙ ε ≡ m
      lawIdL : (m : C) → ε ∙ m ≡ m
      lawAssoc : (m n o : C) → (m ∙ n) ∙ o ≡ m ∙ (n ∙ o)
  
    carrier : Set k
    carrier = C

open Monoid.Monoid {{...}} renaming ( lawIdR to monLawIdR ; lawIdL to monLawIdL ; lawAssoc to monLawAssoc ; carrier to monCarrier )
open Monoid

record EffectMonad (Effect : Set) {{effectMonoid : Monoid Effect}} (M : Effect → TyCon) : Set₁ where
  field
    _>>=_ : ∀ {α β : Type} {i j : Effect} → M i α → (α → M j β) → M (i ∙ j) β
    return : ∀ {α : Type} → α → M ε α
    
    lawIdL : ∀ {α β : Type} {i : Effect}
           → (a : α) → (k : α → M i β) 
           → return a >>= k ≡ subst₂ M (sym (monLawIdL i)) refl (k a)
    lawIdR : ∀ {α : Type} {i : Effect}
           → (m : M i α)
           → m >>= return ≡ subst₂ M (sym (monLawIdR i)) refl m
    lawAssoc : ∀ {α β γ : Type} {i j k : Effect}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≡ subst₂ M (monLawAssoc i j k) refl ((m >>= f) >>= g)
  
  _>>_ : ∀ {α β : Type} {i j : Effect} → M i α → M j β → M (i ∙ j) β
  ma >> mb = ma >>= λ a → mb

data EffMonadTyCons (Effect : Set) : Set where
  EffMonadTC : Effect → EffMonadTyCons Effect

data EffMonadBinds (Effect : Set) {{effectMonoid : Monoid Effect}} : (M N P : IdTyCons ⊎ EffMonadTyCons Effect) → Set where
  MonadB   : ∀ {i j} → EffMonadBinds Effect (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC (i ∙ j)))
  FunctorB : ∀ {i} → EffMonadBinds Effect (inj₂ (EffMonadTC i)) idTC (inj₂ (EffMonadTC i))
  ApplyB   : ∀ {i} → EffMonadBinds Effect idTC (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC i))
  ReturnB  : EffMonadBinds Effect idTC idTC (inj₂ (EffMonadTC ε)) 

open EffectMonad renaming (_>>=_ to mBind; return to mReturn; lawAssoc to mLawAssoc)

bindMonad : ∀ {Effect : Set} {M : Effect → TyCon} {i j : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
          → [ M i , M j ]▷ M (i ∙ j)
bindMonad m = mBind m

bindFunctor : ∀ {Effect : Set} {M : Effect → TyCon} {i : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
            → [ M i , Identity ]▷ M i
bindFunctor {M = M} {i = i} m ma f = subst₂ M (monLawIdR i) refl (mBind m ma (λ a → mReturn m (f a)))

bindApply : ∀ {Effect : Set} {M : Effect → TyCon} {i : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
          → [ Identity , M i ]▷ M i
bindApply {M = M} {i = i} m ma f = subst₂ M (monLawIdL i) refl (mBind m (mReturn m ma) f)

bindReturn : ∀ {Effect : Set} {M : Effect → TyCon} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
           → [ Identity , Identity ]▷ M ε
bindReturn m ma f = mReturn m (f ma)

EffectMonad→Polymonad : ∀ {Effect : Set} {M : Effect → TyCon}
                  → {{effMonoid : Monoid Effect}}
                  → (monad : EffectMonad Effect M)
                  → Polymonad (IdTyCons ⊎ EffMonadTyCons Effect) idTC
EffectMonad→Polymonad {Effect = Effect} {M = M'} monad = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = {!!} --lawFunctor2
  ; lawMorph1 = {!!} --lawMorph1 
  ; lawMorph2 = {!!} --lawMorph2
  ; lawMorph3 = {!!} --lawMorph3
  ; lawDiamond1 = {!!} --lawDiamond1 
  ; lawDiamond2 = {!!} --lawDiamond2
  ; lawAssoc = {!!} --lawAssoc
  ; lawClosure = {!!} --lawClosure
  } where
    TyCons = IdTyCons ⊎ EffMonadTyCons Effect
    
    Id = idTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ (EffMonadTC i)) = M' i
    
    B[_,_]▷_ : TyCons → TyCons → TyCons → Set
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ m            , n            ]▷ inj₁ IdentTC = ⊥
    B[ inj₁ IdentTC        , inj₁ IdentTC        ]▷ inj₂ (EffMonadTC k) = EffMonadBinds Effect idTC                  idTC                  (inj₂ (EffMonadTC k))
    B[ inj₁ IdentTC        , inj₂ (EffMonadTC j) ]▷ inj₂ (EffMonadTC k) = EffMonadBinds Effect idTC                  (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC k))
    B[ inj₂ (EffMonadTC i) , inj₁ IdentTC        ]▷ inj₂ (EffMonadTC k) = EffMonadBinds Effect (inj₂ (EffMonadTC i)) idTC                  (inj₂ (EffMonadTC k))
    B[ inj₂ (EffMonadTC i) , inj₂ (EffMonadTC j) ]▷ inj₂ (EffMonadTC k) = EffMonadBinds Effect (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC k))
    
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC)        (inj₁ IdentTC)        (inj₁ IdentTC)         IdentB   = bindId
    bind (inj₁ IdentTC)        (inj₁ IdentTC)        (inj₂ (EffMonadTC ._)) ReturnB  = bindReturn monad
    bind (inj₁ IdentTC)        (inj₂ (EffMonadTC j)) (inj₁ IdentTC)         ()
    bind (inj₁ IdentTC)        (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC .j)) ApplyB   = bindApply monad
    bind (inj₂ (EffMonadTC i)) (inj₁ IdentTC)        (inj₁ IdentTC)         ()
    bind (inj₂ (EffMonadTC i)) (inj₁ IdentTC)        (inj₂ (EffMonadTC .i)) FunctorB = bindFunctor monad
    bind (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₁ IdentTC)         ()
    bind (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC ._)) MonadB   = bindMonad monad
    
    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC)        = IdentB
    lawFunctor1 (inj₂ (EffMonadTC i)) = FunctorB
    
    lawFunctor2 : ∀ (M : TyCons) → (b : B[ M , Id ]▷ M) 
               → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ (EffMonadTC i)) FunctorB m = lawIdR {!!} m

    -- (mBind m (λ a → mReturn m (id a))) ≡ m

