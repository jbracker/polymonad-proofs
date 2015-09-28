 
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
EffectMonad→Polymonad {Effect = Effect} {M = M'} {{effMonoid = mon}} monad = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
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

    subst₂²≡id : ∀ {a b k} {A : Set a} {B : Set b} {X₁ X₂ : A} {Y₁ Y₂ : B}
          → (P : A → B → Set k)
          → (eqA : X₁ ≡ X₂) (eqB : Y₁ ≡ Y₂)
          → ∀ {z : P X₂ Y₂}
          → z ≡ subst₂ P eqA eqB (subst₂ P (sym eqA) (sym eqB) z)
    subst₂²≡id P refl refl = refl
    
    lawFunctor2 : ∀ (M : TyCons) → (b : B[ M , Id ]▷ M) 
               → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ (EffMonadTC i)) FunctorB m = begin
      (bind (inj₂ (EffMonadTC i)) Id (inj₂ (EffMonadTC i)) FunctorB) m (id lawId)
        ≡⟨ refl ⟩
      (bindFunctor monad) m (id lawId)
        ≡⟨ refl ⟩
      subst₂ M' (monLawIdR i) refl (mBind monad m (λ a → mReturn monad (id lawId a)))
        ≡⟨ refl ⟩
      subst₂ M' (monLawIdR i) refl (mBind monad m (mReturn monad))
        ≡⟨ cong (\X → subst₂ M' (monLawIdR i) refl X) (lawIdR monad m) ⟩
      subst₂ M' (monLawIdR i) refl (subst₂ M' (sym (monLawIdR i)) refl m)
        ≡⟨ sym (subst₂²≡id M' (monLawIdR i) refl) ⟩
      m ∎

    
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) ReturnB = ReturnB
    lawMorph1 (inj₂ (EffMonadTC i)) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC .i)) FunctorB = ApplyB

    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) ReturnB = ReturnB
    lawMorph2 (inj₂ (EffMonadTC i)) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC .i)) ApplyB = FunctorB

    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) (id lawId v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) ReturnB ReturnB v f = refl
    lawMorph3 (inj₂ (EffMonadTC i)) (inj₁ IdentTC) () b₂ v f
    lawMorph3 (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC .i)) FunctorB ApplyB v f = begin
      bindFunctor monad (f v) (id lawId)
        ≡⟨ refl ⟩
      subst₂ M' (monLawIdR i) refl (mBind monad (f v) (mReturn monad))
        ≡⟨ lawFunctor2 (inj₂ (EffMonadTC i)) FunctorB (f v) ⟩
      f v
        ≡⟨ subst₂²≡id M' (monLawIdL i) refl ⟩
      subst₂ M' (monLawIdL i) refl (subst₂ M' (sym (monLawIdL i)) refl (f v))
        ≡⟨ cong (\X → subst₂ M' (monLawIdL i) refl X) (sym (lawIdL monad v f)) ⟩
      subst₂ M' (monLawIdL i) refl (mBind monad (mReturn monad v) f)
        ≡⟨ refl ⟩
      bindApply monad (id lawId v) f ∎

    castMonadB : (x y : monCarrier) {k z : monCarrier}
               → k ≡ z
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC k)
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC z)
    castMonadB x y k≡z b
      = subst (λ X → EffMonadBinds Effect (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC X))) k≡z b
    {-
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) 
      = inj₁ IdentTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (EffMonadTC x)) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , () , b₂)
    lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x) , b₁ , ())
    lawDiamond1 M N (inj₂ (EffMonadTC i)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , ())
    lawDiamond1 M N (inj₂ (EffMonadTC i)) (inj₁ IdentTC) (inj₂ y , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC , IdentB , ReturnB) 
      = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC , IdentB , ApplyB) 
      = inj₂ (EffMonadTC x) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) R (inj₂ (EffMonadTC i)) (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (EffMonadTC j)) (inj₁ IdentTC) R (inj₂ (EffMonadTC i)) (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) R (inj₂ (EffMonadTC k)) (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , ReturnB , FunctorB) 
      = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x) , ApplyB , FunctorB) 
      = inj₂ (EffMonadTC x) , FunctorB , ApplyB
    lawDiamond1 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x) , FunctorB , FunctorB) 
      = inj₂ (EffMonadTC ε) , ReturnB , castMonadB x ε (monLawIdR x) MonadB
    lawDiamond1 (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , MonadB , FunctorB) 
      = inj₂ (EffMonadTC y) , FunctorB , MonadB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , ReturnB , MonadB) 
      = inj₂ (EffMonadTC x) , ApplyB , subst (λ X → EffMonadBinds Effect idTC (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC X))) (sym (monLawIdL x)) ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .x) , ApplyB , MonadB) 
      = inj₂ (EffMonadTC (x ∙ y)) , MonadB , ApplyB
    lawDiamond1 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .x) , FunctorB , MonadB) 
      = inj₂ (EffMonadTC y) , ApplyB , MonadB
    lawDiamond1 (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC z)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , MonadB , MonadB) 
      = inj₂ (EffMonadTC (y ∙ z)) , MonadB , castMonadB x (y ∙ z) (sym (monLawAssoc x y z)) MonadB

    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) 
      = inj₁ IdentTC , IdentB , IdentB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC , IdentB , ReturnB) 
      = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC , IdentB , FunctorB) 
      = (inj₂ (EffMonadTC x)) , FunctorB , FunctorB
    lawDiamond2 M (inj₁ IdentTC) (inj₂ (EffMonadTC x)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (EffMonadTC x)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond2 (inj₁ IdentTC) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x₁) , b₁ , ())
    lawDiamond2 (inj₂ (EffMonadTC x)) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x₁) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , ReturnB , ApplyB)
      = (inj₂ (EffMonadTC ε)) , ReturnB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x) , FunctorB , ApplyB) 
      = inj₂ (EffMonadTC x) , ApplyB , FunctorB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , ReturnB , MonadB) 
      = inj₂ (EffMonadTC x) , FunctorB , subst (λ X → EffMonadBinds Effect (inj₂ (EffMonadTC x)) idTC (inj₂ (EffMonadTC X))) (sym (monLawIdR x)) FunctorB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .y) , FunctorB , MonadB)
      = inj₂ (EffMonadTC (x ∙ y)) , MonadB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x₁) , ApplyB , ())
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x₁) , ApplyB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC .x₁)) (inj₂ (EffMonadTC .x₁) , ApplyB , ApplyB) 
      = inj₁ IdentTC , IdentB , ApplyB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .y) , ApplyB , MonadB) 
      = inj₂ (EffMonadTC x) , FunctorB , MonadB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC x₂)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._) , MonadB , ())
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC x₂)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._) , MonadB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , MonadB , ApplyB) 
      = inj₂ (EffMonadTC x) , ApplyB , MonadB
    lawDiamond2 (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC z)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._) , MonadB , MonadB) 
      = inj₂ (EffMonadTC (x ∙ y)) , MonadB , (castMonadB (x ∙ y) z (monLawAssoc x y z) MonadB)
-}
    lawAssoc : ∀ (M N P R T S : TyCons) 
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc M N P R T S b₁ b₂ b₃ b₄ m f g = {!!}
