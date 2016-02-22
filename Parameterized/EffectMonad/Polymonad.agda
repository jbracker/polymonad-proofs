 
module Parameterized.EffectMonad.Polymonad where

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
open import Parameterized.EffectMonad


open Monoid.Monoid {{...}} renaming ( lawIdR to monLawIdR ; lawIdL to monLawIdL ; lawAssoc to monLawAssoc ; carrier to monCarrier )
open Monoid
open EffectMonad renaming (_>>=_ to mBind; return to mReturn; lawAssoc to mLawAssoc; symLawAssoc to mSymLawAssoc)

subst₂²≡id : ∀ {a b k} {A : Set a} {B : Set b} {X₁ X₂ : A} {Y₁ Y₂ : B}
           → (P : A → B → Set k)
           → (eqA : X₁ ≡ X₂) (eqB : Y₁ ≡ Y₂)
           → ∀ {z : P X₂ Y₂}
           → z ≡ subst₂ P eqA eqB (subst₂ P (sym eqA) (sym eqB) z)
subst₂²≡id P refl refl = refl

subst₂²≡id' : ∀ {a b k} {A : Set a} {B : Set b} {X₁ X₂ : A} {Y₁ Y₂ : B}
            → (P : A → B → Set k)
            → (eqA : X₁ ≡ X₂) (eqB : Y₁ ≡ Y₂)
            → ∀ {z : P X₁ Y₁}
            → z ≡ subst₂ P (sym eqA) (sym eqB) (subst₂ P eqA eqB z)
subst₂²≡id' P refl refl = refl

flipEffectMonadLawAssoc : ∀ {Effect : Set}  {{effectMonoid : Monoid Effect}} {M : Effect → TyCon} 
                        → (monad : EffectMonad Effect M) 
                        → {α β γ : Type} {i j k : Effect}
                        → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
                        → subst₂ M (sym (monLawAssoc i j k)) refl (mBind monad m (λ x → mBind monad (f x) g)) ≡ mBind monad (mBind monad m f) g
flipEffectMonadLawAssoc {M = M} monad {i = i} {j = j} {k = k} m f g = 
  let p = cong (subst₂ M (sym (monLawAssoc i j k)) refl) (mLawAssoc monad m f g)  
  in trans p (sym (subst₂²≡id' M (monLawAssoc i j k) refl))


EffectMonad→Polymonad : ∀ {Effect : Set} {M : Effect → TyCon}
                  → {{effMonoid : Monoid Effect}}
                  → (monad : EffectMonad Effect M)
                  → Polymonad (IdTyCons ⊎ EffMonadTyCons Effect) idTC
EffectMonad→Polymonad {Effect = Effect} {M = M'} {{effMonoid = mon}} monad = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; lawId = lawId
  ; lawFunctor1 = {!!} --lawFunctor1
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
    {-
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC)        = IdentB
    lawFunctor1 (inj₂ (EffMonadTC i)) = FunctorB
    
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
-}
    castMonadB : (x y : monCarrier) {k z : monCarrier}
               → k ≡ z
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC k)
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC z)
    castMonadB x y k≡z b
      = subst (λ X → EffMonadBinds Effect (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC X))) k≡z b

    monEq≡monEq : ∀ {x y : monCarrier} → (p : x ≡ y) → (q : x ≡ y) → p ≡ q
    monEq≡monEq refl refl = refl

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
    contractSubst₂ : ∀ {α : Type} {x y z : monCarrier} {X : M' z α} 
                   → (p : x ≡ y) → (q : z ≡ x) 
                   → subst₂ M' p refl (subst₂ M' q refl X) ≡ subst₂ M' (trans q p) refl X
    contractSubst₂ refl refl = refl

    proof1 : ∀ {α β : Type} {x y z : Effect} 
           → (m : M' z α) → (g : α → M' y β) 
           → (eqA : z ≡ x)
           → mBind monad (subst₂ M' eqA refl m) g ≡ subst₂ M' (cong (λ X → X ∙ y) eqA) refl (mBind monad m g)
    proof1 m g refl = refl

    proof2 :  ∀ {α β : Type} {x y z : Effect} 
           → (m : M' x α) → (g : α → M' y β)
           → (eqA : y ≡ z)
           → mBind monad m (λ y → subst₂ M' eqA refl (g y))
           ≡ subst₂ M' (cong (λ X → x ∙ X) eqA) refl (mBind monad m (λ y → g y))
    proof2 m g refl = refl

    
    proof3 : (x y : monCarrier) → {k z : monCarrier} → (k≡z : k ≡ z) 
           → (b : B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC k)) 
           → b ≡ subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC X)) (sym k≡z) (castMonadB x y k≡z b)
    proof3 x y refl MonadB = refl

    proof4 : {x y z : monCarrier} 
           → (b : EffMonadBinds Effect (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))))
           → castMonadB x (y ∙ z) (Monoid.lawAssoc mon x y z) b ≡ MonadB
    proof4 {x = x} {y = y} {z = z} b with castMonadB x (y ∙ z) (monLawAssoc x y z) b
    proof4 b | MonadB = refl

    switchSubst : ∀ {i j : Effect} {α : Type} 
                → (i≡j : i ≡ j)
                → (m : M' i α)
                → subst₂ M' i≡j refl m
                  ≡ subst (λ X → ⟨ inj₂ (EffMonadTC X) ⟩ α ) i≡j m
    switchSubst refl m = refl
    
    proof5 : ∀ {x u v : Effect} {α β : Type}
           → (eqAssoc : x ∙ u ≡ v)
           → (m : M' x α ) → (f : α → M' u β)
           → subst (λ X → ⟨ inj₂ (EffMonadTC X) ⟩ β ) eqAssoc (mBind monad m f)
             ≡ bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC u)) (inj₂ (EffMonadTC v)) 
                    (subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC u) ]▷ inj₂ (EffMonadTC X)) eqAssoc MonadB) 
                    m f
    proof5 refl m f = refl

    lawAssoc : ∀ (M N P R T S : TyCons) 
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) IdentB () b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ (EffMonadTC x)) b₁ b₂ b₃ () m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ y) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) IdentB b₂ () ReturnB m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) IdentB ReturnB ReturnB ApplyB m f g 
      = {-begin
        bindReturn monad (bindId m f) g
          ≡⟨ refl ⟩
        mReturn monad (g (f m))
          ≡⟨ subst₂²≡id M' (monLawIdL ε) refl ⟩
        subst₂ M' (monLawIdL ε) refl (subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f m))))
          ≡⟨ cong (\X → subst₂ M' (monLawIdL ε) refl X) (sym (lawIdL monad m (λ x → mReturn monad (g (f x))))) ⟩
        subst₂ M' (monLawIdL ε) refl (mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x))))
          ≡⟨ refl ⟩
        bindApply monad m (λ x → bindReturn monad (f x) g) ∎-} {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x)) IdentB ApplyB ApplyB ApplyB m f g 
      = {-begin
        bindApply monad (bindId m f) g
          ≡⟨ refl ⟩
        subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad (f m)) g)
          ≡⟨ subst₂²≡id M' (monLawIdL x) refl ⟩
        subst₂ M' (monLawIdL x) refl (subst₂ M' (sym (monLawIdL x)) refl (subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad (f m)) g)))
          ≡⟨ cong (\X → subst₂ M' (monLawIdL x) refl X) (sym (lawIdL monad m ((λ y → subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad (f y)) g))))) ⟩
        subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad m) (λ y → subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad (f y)) g)))
          ≡⟨ refl ⟩
        bindApply monad m (λ x₁ → bindApply monad (f x₁) g) ∎-} {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc M N (inj₂ (EffMonadTC x)) R (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g 
      = {-begin
          bindFunctor monad (bindReturn monad m f) g 
            ≡⟨ refl ⟩
          subst₂ M' (monLawIdR ε) refl (mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a)))
            ≡⟨ cong (\X → subst₂ M' (monLawIdR ε) refl X) (lawIdL monad (f m) (λ a → mReturn monad (g a))) ⟩
          subst₂ M' (monLawIdR ε) refl (subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f m))))
            ≡⟨ cong (\X → subst₂ M' X refl (subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f m))))) (monEq≡monEq (monLawIdR ε) (monLawIdL ε)) ⟩
          subst₂ M' (monLawIdL ε) refl (subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f m))))
            ≡⟨ sym (subst₂²≡id M' (monLawIdL ε) refl) ⟩
          mReturn monad (g (f m))
            ≡⟨ refl ⟩
          bindReturn monad m (λ x → bindId (f x) g) ∎-} {!!}
    lawAssoc (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) FunctorB FunctorB IdentB FunctorB m f g 
      = {-begin 
        bindFunctor monad (bindFunctor monad m f) g 
          ≡⟨ refl ⟩
        subst₂ M' (monLawIdR x) refl (mBind monad (subst₂ M' (monLawIdR x) refl (mBind monad m (λ a → mReturn monad (f a)))) (λ a → mReturn monad (g a)))
          ≡⟨ cong (subst₂ M' (monLawIdR x) refl) (proof1 (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a)) (monLawIdR x)) ⟩
        subst₂ M' (monLawIdR x) refl (subst₂ M' (cong (λ X → X ∙ ε) (monLawIdR x)) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))))
          ≡⟨ cong (λ X → subst₂ M' (monLawIdR x) refl (subst₂ M' X refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))))) 
                  (monEq≡monEq ((cong (λ X → X ∙ ε) (monLawIdR x))) ((monLawIdR (x ∙ ε)))) ⟩
        subst₂ M' (monLawIdR x) refl (subst₂ M' (monLawIdR (x ∙ ε)) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))))
          ≡⟨ contractSubst₂ (monLawIdR x) (monLawIdR (x ∙ ε)) ⟩
        subst₂ M' (trans (monLawIdR (x ∙ ε)) (monLawIdR x)) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a)))
          ≡⟨ cong (λ X → subst₂ M' (trans (monLawIdR (x ∙ ε)) (monLawIdR x)) refl X) 
                  (sym (flipEffectMonadLawAssoc monad m ((λ a → mReturn monad (f a))) ((λ a → mReturn monad (g a))))) ⟩
        subst₂ M' (trans (monLawIdR (x ∙ ε)) (monLawIdR x)) refl (subst₂ M' (sym (monLawAssoc x ε ε)) refl 
               (mBind monad m (λ x → mBind monad (mReturn monad (f x)) (λ a → mReturn monad (g a)))))
          ≡⟨ contractSubst₂ (trans (monLawIdR (x ∙ ε)) (monLawIdR x)) (sym (monLawAssoc x ε ε)) ⟩
        subst₂ M' (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) refl
               (mBind monad m (λ x → mBind monad (mReturn monad (f x)) (λ a → mReturn monad (g a))))
          ≡⟨ cong (λ X → subst₂ M' (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) refl (mBind monad m X)) 
                  (funExt (λ x → lawIdL monad (f x) (λ a → mReturn monad (g a)))) ⟩
        subst₂ M' (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) refl
               (mBind monad m (λ y → subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f y)))))
          ≡⟨ cong (λ X → subst₂ M' (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) refl X) 
                  (proof2 m (λ y → (mReturn monad (g (f y)))) (sym (monLawIdL ε))) ⟩
        subst₂ M' (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) refl 
               (subst₂ M' (cong (λ X → x ∙ X) (sym (monLawIdL ε))) refl (mBind monad m (λ y → (mReturn monad (g (f y))))))
          ≡⟨ contractSubst₂ (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))) (cong (λ X → x ∙ X) (sym (monLawIdL ε))) ⟩
        subst₂ M' (trans (cong (λ X → x ∙ X) (sym (monLawIdL ε))) (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x)))) refl 
               (mBind monad m (λ y → (mReturn monad (g (f y)))))
          ≡⟨ cong (λ X → subst₂ M' X refl (mBind monad m (λ a → mReturn monad (g (f a))))) 
                  (monEq≡monEq (trans (cong (λ X → x ∙ X) (sym (monLawIdL ε))) (trans (sym (monLawAssoc x ε ε)) (trans (monLawIdR (x ∙ ε)) (monLawIdR x))))
                               (monLawIdR x)) ⟩
        subst₂ M' (monLawIdR x) refl (mBind monad m (λ a → mReturn monad (g (f a))))
          ≡⟨ refl ⟩
        bindFunctor monad m (λ y → bindId (f y) g) ∎-} {!!}
    lawAssoc M (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC x₂)) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc M (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC x₁)) R (inj₂ (EffMonadTC x₂)) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) ReturnB FunctorB ReturnB ApplyB m f g 
      = {-begin
        bindFunctor monad (bindReturn monad m f) g
          ≡⟨ refl ⟩
        subst₂ M' (monLawIdR ε) refl (mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a)))
          ≡⟨ cong (λ X → subst₂ M' X refl (mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a)))) (monEq≡monEq (monLawIdR ε) (monLawIdL ε)) ⟩
        subst₂ M' (monLawIdL ε) refl (mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a)))
          ≡⟨ cong (subst₂ M' (monLawIdL ε) refl) (lawIdL monad (f m) (λ a → mReturn monad (g a))) ⟩
        subst₂ M' (monLawIdL ε) refl (subst₂ M' (sym (monLawIdL ε)) refl (mReturn monad (g (f m))))
          ≡⟨ cong (subst₂ M' (monLawIdL ε) refl) (sym (lawIdL monad m (λ a → mReturn monad (g (f a))))) ⟩
        subst₂ M' (monLawIdL ε) refl (mBind monad (mReturn monad m) (λ a → mReturn monad (g (f a))))
          ≡⟨ refl ⟩
        bindApply monad m (λ a → bindReturn monad (f a) g) ∎-} {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x)) ApplyB FunctorB FunctorB ApplyB m f g 
      = {-begin
        bindFunctor monad (bindApply monad m f) g
          ≡⟨ refl ⟩
        subst₂ M' (monLawIdR x) refl (mBind monad (subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad m) f)) (λ a → mReturn monad (g a)))
          ≡⟨ cong (λ X → subst₂ M' (monLawIdR x) refl (mBind monad (subst₂ M' (monLawIdL x) refl X) (λ a → mReturn monad (g a)))) (lawIdL monad m f) ⟩
        subst₂ M' (monLawIdR x) refl (mBind monad (subst₂ M' (monLawIdL x) refl (subst₂ M' (sym (monLawIdL x)) refl (f m))) (λ a → mReturn monad (g a)))
          ≡⟨ cong (λ X → subst₂ M' (monLawIdR x) refl (mBind monad X (λ a → mReturn monad (g a)))) (sym (subst₂²≡id M' (monLawIdL x) refl)) ⟩
        subst₂ M' (monLawIdR x) refl (mBind monad (f m) (λ a → mReturn monad (g a)))
          ≡⟨ subst₂²≡id M' (monLawIdL x) refl ⟩
        subst₂ M' (monLawIdL x) refl (subst₂ M' (sym (monLawIdL x)) refl (subst₂ M' (monLawIdR x) refl (mBind monad (f m) (λ a → mReturn monad (g a)))))
          ≡⟨ cong (subst₂ M' (monLawIdL x) refl) (sym (lawIdL monad m (λ y → subst₂ M' (monLawIdR x) refl (mBind monad (f y) (λ a → mReturn monad (g a)))))) ⟩
        subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad m) (λ y → subst₂ M' (monLawIdR x) refl (mBind monad (f y) (λ a → mReturn monad (g a)))))
          ≡⟨ refl ⟩
        bindApply monad m (λ y → bindFunctor monad (f y) g) ∎-} {!!}
    lawAssoc (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC ._)) FunctorB FunctorB ReturnB b₄ m f g
      = {!!}
    lawAssoc (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .y)) MonadB FunctorB FunctorB MonadB m f g 
      = {-begin
        bindFunctor monad (bindMonad monad m f) g 
          ≡⟨ refl ⟩
        subst₂ M' (monLawIdR (x ∙ y)) refl (mBind monad (mBind monad m f) (λ a → mReturn monad (g a)))
          ≡⟨ cong (λ X → subst₂ M' X refl (mBind monad (mBind monad m f) (λ a → mReturn monad (g a)))) 
                  (monEq≡monEq (monLawIdR (x ∙ y)) (trans (monLawAssoc x y ε) (cong (λ X → x ∙ X) (monLawIdR y)))) ⟩
        subst₂ M' (trans (monLawAssoc x y ε) (cong (λ X → x ∙ X) (monLawIdR y))) refl (mBind monad (mBind monad m f) (λ b → mReturn monad (g b)))
          ≡⟨ sym (contractSubst₂ ((cong (λ X → x ∙ X) (monLawIdR y))) ((monLawAssoc x y ε))) ⟩
        subst₂ M' (cong (λ X → x ∙ X) (monLawIdR y)) refl (subst₂ M' (monLawAssoc x y ε) refl (mBind monad (mBind monad m f) (λ b → mReturn monad (g b))))
          ≡⟨ cong (λ X → subst₂ M' (cong (λ X → x ∙ X) (monLawIdR y)) refl X) (sym (mLawAssoc monad m f (λ b → mReturn monad (g b)))) ⟩
        subst₂ M' (cong (λ X → x ∙ X) (monLawIdR y)) refl (mBind monad m (λ a → mBind monad (f a) (λ b → mReturn monad (g b))))
          ≡⟨ sym (proof2 m (λ a → (mBind monad (f a) (λ b → mReturn monad (g b)))) (monLawIdR y)) ⟩
        mBind monad m (λ a → subst₂ M' (monLawIdR y) refl (mBind monad (f a) (λ b → mReturn monad (g b))))
          ≡⟨ refl ⟩
        bindMonad monad m (λ x₁ → bindFunctor monad (f x₁) g) ∎-} {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC x₂)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) ReturnB MonadB b₃ ApplyB m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) ApplyB MonadB MonadB ApplyB m f g 
      = {-begin
        bindMonad monad (bindApply monad m f) g 
          ≡⟨ refl ⟩
        mBind monad (subst₂ M' (monLawIdL x) refl (mBind monad (mReturn monad m) f)) g 
          ≡⟨ proof1 (mBind monad (mReturn monad m) f) g (monLawIdL x) ⟩
        subst₂ M' (cong (λ X → X ∙ y) (monLawIdL x)) refl (mBind monad (mBind monad (mReturn monad m) f) g)
          ≡⟨ cong (λ X → subst₂ M' (cong (λ X → X ∙ y) (monLawIdL x)) refl (mBind monad X g)) (lawIdL monad m f) ⟩
        subst₂ M' (cong (λ X → X ∙ y) (monLawIdL x)) refl (mBind monad (subst₂ M' (sym (monLawIdL x)) refl (f m)) g)
          ≡⟨ cong (λ X → subst₂ M' (cong (λ X → X ∙ y) (monLawIdL x)) refl X) (proof1 (f m) g (sym (monLawIdL x))) ⟩
        subst₂ M' (cong (λ X → X ∙ y) (monLawIdL x)) refl (subst₂ M' (cong (λ X → X ∙ y) (sym (monLawIdL x))) refl (mBind monad (f m) g))
          ≡⟨ contractSubst₂ (cong (λ X → X ∙ y) (monLawIdL x)) (cong (λ X → X ∙ y) (sym (monLawIdL x))) ⟩
        subst₂ M' (trans (cong (λ X → X ∙ y) (sym (monLawIdL x))) (cong (λ X → X ∙ y) (monLawIdL x))) refl (mBind monad (f m) g)
          ≡⟨ cong (λ X → subst₂ M' X refl (mBind monad (f m) g)) (monEq≡monEq (trans (cong (λ X → X ∙ y) (sym (monLawIdL x))) (cong (λ X → X ∙ y) (monLawIdL x))) refl) ⟩
        subst₂ M' refl refl (mBind monad (f m) g)
          ≡⟨ refl ⟩
        mBind monad (f m) g
          ≡⟨ subst₂²≡id M' (monLawIdL (x ∙ y)) refl ⟩
        subst₂ M' (monLawIdL (x ∙ y)) refl (subst₂ M' (sym (monLawIdL (x ∙ y))) refl (mBind monad (f m) g))
          ≡⟨ cong (λ X → subst₂ M' (monLawIdL (x ∙ y)) refl X) (sym (lawIdL monad m (λ a → mBind monad (f a) g))) ⟩
        subst₂ M' (monLawIdL (x ∙ y)) refl (mBind monad (mReturn monad m) (λ a → mBind monad (f a) g))
          ≡⟨ refl ⟩
        bindApply monad m (λ a → bindMonad monad (f a) g) ∎ -} {!!}
    lawAssoc (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .y)) FunctorB MonadB ApplyB MonadB m f g
      = {-begin
        bindMonad monad (bindFunctor monad m f) g
          ≡⟨ refl ⟩
        mBind monad (subst₂ M' (monLawIdR x) refl (mBind monad m (λ a → mReturn monad (f a)))) g
          ≡⟨ proof1 ((mBind monad m (λ a → mReturn monad (f a)))) g (monLawIdR x) ⟩
        subst₂ M' (cong (λ X → X ∙ y) (monLawIdR x)) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) g)
          ≡⟨ cong (λ X → subst₂ M' X refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) g)) 
                  (monEq≡monEq (cong (λ X → X ∙ y) (monLawIdR x)) (trans (monLawAssoc x ε y) (cong (λ X → x ∙ X) (monLawIdL y)))) ⟩
        subst₂ M' (trans (monLawAssoc x ε y) (cong (λ X → x ∙ X) (monLawIdL y))) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) g)
          ≡⟨ sym (contractSubst₂ (cong (λ X → x ∙ X) (monLawIdL y)) (monLawAssoc x ε y)) ⟩
        subst₂ M' (cong (λ X → x ∙ X) (monLawIdL y)) refl (subst₂ M' (monLawAssoc x ε y) refl (mBind monad (mBind monad m (λ a → mReturn monad (f a))) g))
          ≡⟨ cong (λ X → subst₂ M' (cong (λ X → x ∙ X) (monLawIdL y)) refl X) (sym (mLawAssoc monad m (λ a → mReturn monad (f a)) g)) ⟩
        subst₂ M' (cong (λ X → x ∙ X) (monLawIdL y)) refl (mBind monad m (λ a → mBind monad (mReturn monad (f a)) g))
          ≡⟨ sym (proof2 m (λ a → mBind monad (mReturn monad (f a)) g) (monLawIdL y)) ⟩
        mBind monad m (λ a → subst₂ M' (monLawIdL y) refl (mBind monad (mReturn monad (f a)) g))
          ≡⟨ refl ⟩
        bindMonad monad m (λ a → bindApply monad (f a) g) ∎ -} {!!}
    lawAssoc (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC z)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) MonadB MonadB MonadB b₄ m f g 
      with castMonadB x (y ∙ z) (monLawAssoc x y z) b₄
    lawAssoc (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC y)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC z)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) MonadB MonadB MonadB b₄ {γ = γ} m f g | MonadB
      = let b = bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))) b₄
        in begin
          bindMonad monad (bindMonad monad m f) g 
            ≡⟨ refl ⟩
          mBind monad (mBind monad m f) g 
            ≡⟨ sym (mSymLawAssoc monad m f g) ⟩
          subst₂ M' (sym (monLawAssoc x y z)) refl (mBind monad m (λ x → mBind monad (f x) g))
            ≡⟨ switchSubst (sym (monLawAssoc x y z)) (mBind monad m (λ x → mBind monad (f x) g)) ⟩
          subst (λ X → ⟨ inj₂ (EffMonadTC X) ⟩ γ ) (sym (monLawAssoc x y z)) (mBind monad m (λ x → mBind monad (f x) g))
            ≡⟨ proof5 (sym (monLawAssoc x y z)) m ((λ x → mBind monad (f x) g)) ⟩
          bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))) 
               (subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC (y ∙ z)) ]▷ inj₂ (EffMonadTC X)) (sym (monLawAssoc x y z)) MonadB) 
               m (λ x₂ → mBind monad (f x₂) g)
            ≡⟨ cong (λ X → bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))) 
                           (subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC (y ∙ z)) ]▷ inj₂ (EffMonadTC X)) (sym (monLawAssoc x y z)) X) 
                           m (λ x₂ → mBind monad (f x₂) g)) 
                    (sym (proof4 b₄)) ⟩
          bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))) 
               (subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC (y ∙ z)) ]▷ inj₂ (EffMonadTC X)) (sym (monLawAssoc x y z)) (castMonadB x (y ∙ z) (monLawAssoc x y z) b₄)) 
               m (λ x₂ → mBind monad (f x₂) g)
            ≡⟨ cong (λ X → bind (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC (y ∙ z))) (inj₂ (EffMonadTC ((x ∙ y) ∙ z))) X m (λ x₂ → mBind monad (f x₂) g)) 
                    (sym (proof3 x (y ∙ z) (monLawAssoc x y z) b₄)) ⟩
          b m (λ x₂ → mBind monad (f x₂) g)
            ≡⟨ refl ⟩
          b m (λ x₂ → bindMonad monad (f x₂) g) ∎

{-
proof3 : (x y : monCarrier) → {k z : monCarrier} → (k≡z : k ≡ z) 
           → (b : B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC k)) 
           → b ≡ subst (λ X → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC X)) (sym k≡z) (castMonadB x y k≡z b)
-}
{-
castMonadB : (x y : monCarrier) {k z : monCarrier}
               → k ≡ z
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC k)
               → B[ inj₂ (EffMonadTC x) , inj₂ (EffMonadTC y) ]▷ inj₂ (EffMonadTC z)
-}
{-
lawIdR : ∀ {α : Type} {i : Effect}
           → (m : M i α)
           → m >>= return ≡ subst₂ M (sym (monLawIdR i)) refl m

lawIdL : ∀ {α β : Type} {i : Effect}
           → (a : α) → (k : α → M i β) 
           → return a >>= k ≡ subst₂ M (sym (monLawIdL i)) refl (k a)

lawAssoc : ∀ {α β γ : Type} {i j k : Effect}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≡ subst₂ M (monLawAssoc i j k) refl ((m >>= f) >>= g)
-}
{-
proof1 : ∀ {α β : Type} {x z : Effect} 
           → (m : M' z α) → (g : α → M' ε β) 
           → (eqA : z ≡ x)
           → mBind monad (subst₂ M' eqA refl m) g ≡ subst₂ M' (cong (λ X → X ∙ ε) eqA) refl (mBind monad m g)
proof2 :  ∀ {α β : Type} {x y z : Effect} 
           → (m : M' x α) → (g : α → M' y β)
           → (eqA : y ≡ z)
           → mBind monad m (λ y → subst₂ M' eqA refl (g y))
           ≡ subst₂ M' (cong (λ X → x ∙ X) eqA) refl (mBind monad m (λ y → g y))
-}
-- bindReturn m ma f = mReturn m (f ma)
-- bindApply {M = M} {i = i} m ma f = subst₂ M (monLawIdL i) refl (mBind m (mReturn m ma) f)
-- bindFunctor {M = M} {i = i} m ma f = subst₂ M (monLawIdR i) refl (mBind m ma (λ a → mReturn m (f a)))
{-
subst₂²≡id : ∀ {a b k} {A : Set a} {B : Set b} {X₁ X₂ : A} {Y₁ Y₂ : B}
          → (P : A → B → Set k)
          → (eqA : X₁ ≡ X₂) (eqB : Y₁ ≡ Y₂)
          → ∀ {z : P X₂ Y₂}
          → z ≡ subst₂ P eqA eqB (subst₂ P (sym eqA) (sym eqB) z)
-}

{-
    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (IdentB , IdentB , IdentB , ReturnB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) U (IdentB , () , IdentB , e)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) S (inj₂ (EffMonadTC x)) U (IdentB , c , () , e)
    lawClosure (inj₁ IdentTC) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) S T U (() , c , d , e)
    lawClosure (inj₂ (EffMonadTC x)) N (inj₁ IdentTC) S T U (() , c , d , e)
    lawClosure M N (inj₂ (EffMonadTC x)) S T (inj₁ IdentTC) (b , c , d , ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (ReturnB , () , IdentB , FunctorB)
    lawClosure (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (FunctorB , ReturnB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₂ (EffMonadTC x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x)) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
    lawClosure M (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) S (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC .x₁)) (b , c , () , FunctorB)
    lawClosure (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (ApplyB , IdentB , ReturnB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC .x₁)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x₁)) (inj₂ (EffMonadTC .x₁)) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₁ IdentTC) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC .x₁)) (inj₂ (EffMonadTC x)) T (inj₂ (EffMonadTC .x₁)) (ApplyB , () , d , FunctorB)
    lawClosure (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (MonadB , ReturnB , ReturnB , FunctorB) 
      = subst (λ X → EffMonadBinds Effect Id Id (inj₂ (EffMonadTC X))) (sym (monLawIdR ε)) ReturnB
    lawClosure (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .x)) (inj₁ IdentTC) (inj₂ (EffMonadTC ._)) (MonadB , FunctorB , ReturnB , FunctorB) 
      = subst (λ X → EffMonadBinds Effect (inj₂ (EffMonadTC x)) Id (inj₂ (EffMonadTC X))) (sym (monLawIdR x)) FunctorB
    lawClosure (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC ._)) (inj₁ IdentTC) (inj₂ (EffMonadTC .x₁)) (inj₂ (EffMonadTC ._)) (MonadB , ReturnB , FunctorB , FunctorB) 
      = subst (λ X → EffMonadBinds Effect Id (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC X))) (sym (monLawIdL x₁)) ApplyB
    lawClosure (inj₂ (EffMonadTC x)) (inj₂ (EffMonadTC x₁)) (inj₂ (EffMonadTC ._)) (inj₂ (EffMonadTC .x)) (inj₂ (EffMonadTC .x₁)) (inj₂ (EffMonadTC ._)) (MonadB , FunctorB , FunctorB , FunctorB) 
      = MonadB
-}
