
module KmettMonad.Polymonad where

-- Stdlib
open import Level
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
open import Polymonad
open import KmettMonad.Definition

-- -----------------------------------------------------------------------------
-- Every Kmett Monad is a Polymonad
-- -----------------------------------------------------------------------------

KmettMonad→Polymonad : ∀ {n}
                     → (TyCons : Set n)
                     → KmettMonad TyCons → Polymonad (IdTyCons ⊎ TyCons) idTC
KmettMonad→Polymonad {n = n} KmettTyCons monad = record
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {M} {N} {P} b → bind M N P b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1
  ; lawDiamond2 = lawDiamond2
  ; lawAssoc = lawAssoc
  ; lawClosure = lawClosure
  } where
    TyCons = IdTyCons ⊎ KmettTyCons
    Id = idTC
    
    B[_,_]▷_ : (M N P : TyCons) → Set n
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ P       = KmettBinds monad idTC idTC (inj₂ P)
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₁ IdentTC , inj₂ N       ]▷ inj₂ P       = KmettBinds monad idTC (inj₂ N) (inj₂ P)
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₁ IdentTC ]▷ inj₂ P       = KmettBinds monad (inj₂ M) idTC (inj₂ P)
    B[ inj₂ M       , inj₂ N       ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₂ M       , inj₂ N       ]▷ inj₂ P       = KmettBinds monad (inj₂ M) (inj₂ N) (inj₂ P)
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ M) = K⟨ monad ▷ M ⟩
    
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (ReturnB .M rCompat) = bindReturn M monad rCompat
    bind (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (ApplyB .N) = bindApply N monad
    bind (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M) = bindFunctor M monad
    bind (inj₂ M) (inj₂ N) (inj₁ IdentTC) (lift ())
    bind (inj₂ M) (inj₂ N) (inj₂ ._) (MonadB .M .N bCompat) = bindMonad M N monad bCompat

    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ M) = FunctorB M

    lawFunctor2 : ∀ (M : TyCons) → ∀ (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ M) (FunctorB .M) m = begin
      (bind (inj₂ M) Id (inj₂ M) (FunctorB M)) m (id lawId)
        ≡⟨ refl ⟩
      (bindFunctor M monad) m (id lawId)
        ≡⟨ KmettMonad.lawIdL monad M M {!!} {!!} {!!} m ⟩
      m ∎

    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ M) (ReturnB .M rComp) = ReturnB M rComp
    lawMorph1 (inj₂ M) (inj₁ IdentTC) (lift ())
    lawMorph1 (inj₂ M) (inj₂ .M) (FunctorB .M) = ApplyB M
    
    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ M) (ReturnB .M rComp) = ReturnB M rComp
    lawMorph2 (inj₂ M) (inj₁ IdentTC) (lift ())
    lawMorph2 (inj₂ M) (inj₂ .M) (ApplyB .M) = FunctorB M
    
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) ((id lawId) v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ M) (ReturnB .M rCompat₁) (ReturnB .M rCompat₂) v f = begin
      bindReturn M monad rCompat₁ (f v) (id lawId)
        ≡⟨ refl ⟩
      KmettMonad.return⟨_,_⟩ monad M rCompat₁ (f v)
        ≡⟨ cong (λ X → KmettMonad.return⟨_,_⟩ monad M X (f v)) {!!} ⟩
      KmettMonad.return⟨_,_⟩ monad M rCompat₂ (f v)
        ≡⟨ refl ⟩
      bindReturn M monad rCompat₂ (id lawId v) f ∎
    lawMorph3 (inj₂ M) (inj₁ IdentTC) (lift ()) (lift ()) v f
    lawMorph3 (inj₂ M) (inj₂ .M) (FunctorB .M) (ApplyB .M) v f = begin
      bindFunctor M monad (f v) (id lawId) 
        ≡⟨ refl ⟩
      Functor.fmap (KmettMonad.functor monad M) (id lawId) (f v)
        ≡⟨ cong (λ X → X (f v)) (Functor.lawId (KmettMonad.functor monad M)) ⟩
      f v
        ≡⟨ refl ⟩
      bindApply M monad (id lawId v) f ∎
    
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = idTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC , IdentB , ReturnB .M rCompat) = idTC , IdentB , ReturnB M rCompat
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₁ IdentTC , IdentB , ApplyB .R) = inj₂ R , ApplyB R , ApplyB R
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ M) (inj₂ N) R T (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P , b₁ , lift ())
    lawDiamond1 M N (inj₂ R) (inj₁ IdentTC) (inj₂ P , b₁ , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M , ReturnB .M rCompat , FunctorB .M) = idTC , IdentB , ReturnB M rCompat
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N , ApplyB .N , FunctorB .N) = inj₂ N , FunctorB N , ApplyB N
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M , FunctorB .M , FunctorB .M) = idTC , IdentB , FunctorB M
    lawDiamond1 (inj₂ M) (inj₂ N) (inj₁ IdentTC) (inj₂ ._) (inj₂ ._ , MonadB .M .N bCompat , FunctorB ._) = inj₂ N , FunctorB N , MonadB M N bCompat
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .(M ◆⟨ monad ⟩ R)) (inj₂ M , ReturnB .M rCompat , MonadB .M .R bCompat) = {!!}
    lawDiamond1 (inj₁ IdentTC) (inj₂ N) (inj₂ R) (inj₂ .(N ◆⟨ monad ⟩ R)) (inj₂ .N , ApplyB .N , MonadB .N .R bCompat) = {!!}
    lawDiamond1 (inj₂ M) (inj₁ IdentTC) (inj₂ R) (inj₂ .(M ◆⟨ monad ⟩ R)) (inj₂ .M , FunctorB .M , MonadB .M .R bCompat) = {!!}
    lawDiamond1 (inj₂ M) (inj₂ N) (inj₂ R) (inj₂ .((M ◆⟨ monad ⟩ N) ◆⟨ monad ⟩ R)) (inj₂ ._ , MonadB .M .N bCompat₁ , MonadB ._ .R bCompat₂) = {!!}
    
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = idTC , IdentB , IdentB
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC , IdentB , ReturnB .M rCompat) = idTC , IdentB , ReturnB M rCompat
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC , IdentB , FunctorB .M) = inj₂ M , FunctorB M , FunctorB M
    lawDiamond2 M (inj₁ IdentTC) (inj₂ R) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 M (inj₂ N) (inj₁ IdentTC) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 M (inj₂ N) (inj₂ R) T (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ S , b₁ , lift ())
    lawDiamond2 (inj₂ M) N R (inj₁ IdentTC) (inj₂ S , b₁ , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M , ReturnB .M rCompat , ApplyB .M) = idTC , IdentB , ReturnB M rCompat
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₂ .R , ApplyB .R , ApplyB .R) = idTC , IdentB , ApplyB R
    lawDiamond2 (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N , FunctorB .N , ApplyB .N) = inj₂ N , ApplyB N , FunctorB N
    lawDiamond2 (inj₁ IdentTC) (inj₂ N) (inj₂ R) (inj₂ ._) (inj₂ ._ , MonadB .N .R bCompat , ApplyB ._) = {!!}
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ._) (inj₂ M₁ , ReturnB .M₁ rCompat , MonadB .M .M₁ bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₁ IdentTC) (inj₂ R) (inj₂ ._) (inj₂ .R , ApplyB .R , MonadB .M .R bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₂ N) (inj₁ IdentTC) (inj₂ ._) (inj₂ .N , FunctorB .N , MonadB .M .N bCompat) = {!!}
    lawDiamond2 (inj₂ M) (inj₂ N) (inj₂ R) (inj₂ ._) (inj₂ ._ , MonadB .N .R bCompat₁ , MonadB .M ._ bCompat₂) = {!!}
    
    lawAssoc : ∀ (M N P R T S : TyCons) 
             → (b₁ : B[ M , N ]▷ P) → (b₂ : B[ P , R ]▷ T) 
             → (b₃ : B[ N , R ]▷ S) → (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (lift ()) IdentB IdentB (lift ()) m f g
    lawAssoc M (inj₂ N) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b₁ IdentB (lift ()) b₄ m f g
    lawAssoc (inj₁ IdentTC) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b₁ IdentB b₃ (lift ()) m f g
    lawAssoc (inj₂ M) N (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b₁ IdentB b₃ (lift ()) m f g
    lawAssoc M N (inj₁ IdentTC) (inj₂ R) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc M N (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc M N (inj₂ P) (inj₂ R) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) IdentB (ReturnB .M rCompat₁) IdentB (ReturnB .M rCompat₂) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ R) (inj₂ .R) (inj₁ IdentTC) IdentB (ApplyB .R) (lift ()) (ReturnB .R rCompat) m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M) IdentB (ReturnB .M rCompat₁) (ReturnB .M rCompat₂) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₂ .M) IdentB (ApplyB .M) (ApplyB .M) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₂ M) (inj₂ N) (inj₁ IdentTC) R (inj₂ T) S (lift ()) b₂ b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (ReturnB .M rCompat₁) (FunctorB .M) IdentB (ReturnB .M rCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (FunctorB .M) (FunctorB .M) IdentB (FunctorB .M) m f g
      = {!!}
    lawAssoc M (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc M (inj₂ N) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc M (inj₂ N) (inj₂ P) (inj₂ R) (inj₂ T) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ .P) (inj₂ .P) (ReturnB .P rCompat) (FunctorB .P) (ReturnB .P x) (ApplyB .P) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ ._) (inj₂ ._) (ReturnB .P rCompat) (MonadB .P .R bCompat) b₃ (ApplyB ._) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (ApplyB .M) (FunctorB .M) (FunctorB .M) (ApplyB .M) m f g
      = {!!}
    lawAssoc (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (inj₂ R) (inj₂ ._) (inj₂ ._) (ApplyB .N) (MonadB .N .R bCompat₁) (MonadB .N .R bCompat₂) (ApplyB ._) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (inj₂ S) (FunctorB .M) (FunctorB .M) (ReturnB .S rCompat) b₄ m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ R) (inj₂ ._) (inj₂ .R) (FunctorB .M) (MonadB .M .R bCompat₁) (ApplyB .R) (MonadB .M .R bCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₂ N) (inj₂ ._) (inj₁ IdentTC) (inj₂ ._) (inj₂ .N) (MonadB .M .N bCompat₁) (FunctorB ._) (FunctorB .N) (MonadB .M .N bCompat₂) m f g
      = {!!}
    lawAssoc (inj₂ M) (inj₂ N) (inj₂ ._) (inj₂ R) (inj₂ ._) (inj₂ ._) (MonadB .M .N bCompat₁) (MonadB ._ .R bCompat₂) (MonadB .N .R bCompat₃) b₄ m f g
      = {!!}

   
    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) (IdentB , IdentB , lift () , IdentB)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) T (inj₁ IdentTC) (IdentB , lift () , b₃ , IdentB)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₂ M) (inj₂ N) (inj₁ IdentTC) S T (inj₁ IdentTC) (lift () , b₂ , b₃ , IdentB)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ U) (IdentB , IdentB , IdentB , ReturnB .U rCompat) = ReturnB U rCompat
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) (inj₁ IdentTC) (inj₂ U) (IdentB , lift () , IdentB , ReturnB .U rCompat)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ T) (inj₂ U) (IdentB , IdentB , lift () , ReturnB .U rCompat)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) (inj₂ T) (inj₂ U) (IdentB , lift () , lift () , ReturnB .U rCompat)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , ReturnB .U rCompat)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , ReturnB .U rCompat)
    lawClosure (inj₂ M) (inj₂ N) (inj₁ IdentTC) S T (inj₂ U) (lift () , b₂ , b₃ , ReturnB .U rCompat)
    lawClosure M N (inj₂ P) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , lift ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (ReturnB .M rCompat , IdentB , IdentB , FunctorB .M) = ReturnB M rCompat
    lawClosure (inj₁ IdentTC) (inj₂ M) (inj₂ .M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (ApplyB .M , IdentB , ReturnB .M rCompat , FunctorB .M) = ReturnB M rCompat
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₂ .P) (ReturnB .P rCompat , IdentB , lift () , FunctorB .P)
    lawClosure (inj₁ IdentTC) (inj₂ N) (inj₂ .N) (inj₁ IdentTC) (inj₂ .N) (inj₂ .N) (ApplyB .N , IdentB , FunctorB .N , FunctorB .N) = ApplyB N
    lawClosure (inj₁ IdentTC) N (inj₂ P) (inj₂ S) T (inj₂ .P) (b₁ , lift () , b₃ , FunctorB .P)
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M , ReturnB .M rCompat , IdentB , FunctorB .M) = ReturnB M rCompat
    lawClosure (inj₂ M) (inj₂ N) (inj₂ ._) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ ._) (MonadB .M .N bCompat , ReturnB .M rCompat₁ , ReturnB .N rCompat₂ , FunctorB ._) = {!!}
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₁ IdentTC) (inj₂ T) (inj₂ .M) (FunctorB .M , ReturnB .M rCompat , lift () , FunctorB .M)
    lawClosure (inj₂ M) (inj₂ N) (inj₂ ._) (inj₁ IdentTC) (inj₂ .N) (inj₂ ._) (MonadB .M .N bCompat , ReturnB .M rCompat , FunctorB .N , FunctorB ._) = {!!}
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (inj₁ IdentTC) (inj₂ .M) (FunctorB .M , FunctorB .M , IdentB , FunctorB .M) = FunctorB M
    lawClosure (inj₂ M) (inj₁ IdentTC) (inj₂ .M) (inj₂ .M) (inj₂ T) (inj₂ .M) (FunctorB .M , FunctorB .M , lift () , FunctorB .M)
    lawClosure (inj₂ M) (inj₂ N) (inj₂ ._) (inj₂ .M) (inj₁ IdentTC) (inj₂ ._) (MonadB .M .N bCompat , FunctorB .M , ReturnB .N rCompat , FunctorB ._) = {!!}
    lawClosure (inj₂ M) (inj₂ N) (inj₂ ._) (inj₂ .M) (inj₂ .N) (inj₂ ._) (MonadB .M .N bCompat , FunctorB .M , FunctorB .N , FunctorB ._) = MonadB M N bCompat
