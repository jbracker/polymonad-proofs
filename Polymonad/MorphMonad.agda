 
module Polymonad.MorphMonad where

-- Stdlib
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
open import Polymonad.Composable
open import Polymonad.Principal
open import Monad
open import Monad.Polymonad
open import Monad.Composable
open import Monad.Principal

open import Polymonad.MorphMonad.Types
open import Polymonad.MorphMonad.Diamond1
open import Polymonad.MorphMonad.Diamond2
open import Polymonad.MorphMonad.Closure

-- -----------------------------------------------------------------------------
-- Morph combination of two monads into a polymonad
-- -----------------------------------------------------------------------------

open Monad.Monad

polymonadMorphMonad : ∀ { M₁ M₂ : TyCon } 
                    → (monad₁ : Monad M₁)
                    → Monad M₂
                    → (bindMorph2I1B : [ M₂ , Identity ]▷ M₁)
                    → (bindMorph112 : [ M₁ , M₁ ]▷ M₂)
                    → (∀ {α : Type} → (x : M₁ α) → bindMorph112 x (mReturn monad₁) ≡ bindMorph112 ((mReturn monad₁) x) (id refl))
                    → Polymonad (IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)) idTC
polymonadMorphMonad {M₁ = M₁} {M₂ = M₂} monad₁ monad₂ bindMorph2I1 bindMorph112 morphReturnIdLaw = record
  { B[_,_]▷_ = Morph[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1
  ; lawDiamond2 = lawDiamond2
  ; lawAssoc = lawAssocMorph
  ; lawClosure = lawClosure
  } where
    TyCons = IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)

    
    pm₁ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₁ = Monad→Polymonad monad₁
    
    pm₂ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₂ = Monad→Polymonad monad₂
    
    Id = idTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ (inj₁ MonadTC)) = M₁
    ⟨_⟩ (inj₂ (inj₂ MonadTC)) = M₂
    
    bind : (M N P : TyCons) → Morph[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB = bindReturn monad₁
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB = bindReturn monad₂
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ApplyB = bindApply monad₁
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyMorphB = bindMorphI12 (bindReturn monad₁) bindMorph112
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) MorphI21B = bindMorphI21 bindMorph2I1
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyB = bindApply monad₂
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) FunctorB = bindFunctor monad₁
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) FunctorMorphB = bindMorph1I2 (bindReturn monad₁) bindMorph112
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) MonadB = bindMonad monad₁
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph112B = bindMorph112
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph121B = bindMorph121 bindMorph2I1 bindMorph112
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph122B = bindMorph122 bindMorph2I1 bindMorph112
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) Morph2I1B = bindMorph2I1
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) FunctorB = bindFunctor monad₂
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph211B = bindMorph211 bindMorph2I1 bindMorph112
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph212B = bindMorph212 bindMorph2I1 bindMorph112
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph221B = bindMorph221 bindMorph2I1 bindMorph112
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) MonadB = bindMonad monad₂

    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
 
    lawFunctor1 : ∀ (M : TyCons) → Morph[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ (inj₁ MonadTC)) = FunctorB
    lawFunctor1 (inj₂ (inj₂ MonadTC)) = FunctorB
    
    lawFunctor2 : ∀ (M : TyCons) → (b : Morph[ M , Id ]▷ M) 
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ (inj₁ MonadTC)) FunctorB m = lawIdL monad₁ m
    lawFunctor2 (inj₂ (inj₂ MonadTC)) FunctorB m = lawIdL monad₂ m

    lawMorph1 : ∀ (M N : TyCons) 
              → (Morph[ M , Id ]▷ N → Morph[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) N b = b
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) FunctorB = ApplyB
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph1I2B = MorphI12B
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph2I1B = MorphI21B
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorB = ApplyB

    lawMorph2 : ∀ (M N : TyCons) 
              → (Morph[ Id , M ]▷ N → Morph[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) N b = b
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ApplyB = FunctorB
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) MorphI12B = Morph1I2B
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) MorphI21B = Morph2I1B
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyB = FunctorB
    
    lawMorph3 : ∀ (M N : TyCons) (b₁ : Morph[ M , Id ]▷ N) (b₂ : Morph[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) (id lawId v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) () () v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) () () v f
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB ReturnB v f = pmLawMorph3 pm₁ idTC (inj₂ MonadTC) ReturnB ReturnB v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₁ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph2I1B MorphI21B v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB ReturnB v f = pmLawMorph3 pm₂ idTC (inj₂ MonadTC) ReturnB ReturnB v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph1I2B MorphI12B v f = begin
      bindMorph1I2 (bindReturn monad₁) bindMorph112 (f v) (id lawId)
        ≡⟨ refl ⟩
      bindMorph112 (f v) (λ a → (bindReturn monad₁) ((id lawId) a) (id refl))
        ≡⟨ refl ⟩
      bindMorph112 (f v) (mReturn monad₁)
        ≡⟨ morphReturnIdLaw (f v) ⟩
      bindMorph112 ((mReturn monad₁) (f v)) (id refl)
        ≡⟨ refl ⟩
      bindMorph112 ((bindReturn monad₁) (f (id lawId v)) (id refl)) (id refl)
        ≡⟨ refl ⟩
      bindMorphI12 (bindReturn monad₁) bindMorph112 (id lawId v) f ∎
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₂ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f

    -- bindReturn m ma f = mReturn m (f ma)

    -- bindMorphI12 retB m112B m f = m112B (retB (f m) (id refl)) (id refl)


    -- bindMorph1I2 retB m112B m f = m112B m (λ a → retB (f a) (id refl))

    -- bindMorphI21 m2I1B m f = m2I1B (f m) (id refl)

    lawAssocMorph : ∀ (M N P R T S : MonadMorphTyCons) 
                    (b₁ : Morph[ M , N ]▷ P) (b₂ : Morph[ P , R ]▷ T) 
                    (b₃ : Morph[ N , R ]▷ S) (b₄ : Morph[ M , S ]▷ T)
                  → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
                  → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) IdentB IdentB ReturnB () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) IdentB IdentB ReturnB () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ReturnB ReturnB ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ReturnB ReturnB MorphI21B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ReturnB ReturnB MorphI12B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ReturnB ReturnB ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S IdentB () b3 b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S IdentB () b3 b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) IdentB b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) IdentB b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ApplyB ApplyB ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ApplyB MorphI12B MorphI21B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB MorphI12B ApplyB MorphI12B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB MorphI12B MorphI12B ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB MorphI21B MorphI21B ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB MorphI21B ApplyB MorphI21B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ApplyB MorphI21B MorphI12B m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ApplyB ApplyB ApplyB m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 () IdentB b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 () IdentB b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}

    lawAssocMorph (inj₂ M) N P R T S b1 b2 b3 b4 m f g = {!!} {-
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 IdentB () m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 IdentB () m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ S) b1 Morph211B b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ S) b1 Morph212B b3 b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 Morph122B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 Morph121B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) b1 Morph211B Morph211B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) b1 Morph212B Morph211B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) b1 Morph211B Morph212B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) b1 Morph212B Morph212B b4 m f g = {!!}
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    lawAssocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
   
-}
