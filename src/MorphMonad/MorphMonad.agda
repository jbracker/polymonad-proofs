 
module MorphMonad.MorphMonad where

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
open import Polymonad.Unionable
open import Polymonad.Principal
open import Monad
open import Monad.Polymonad
open import Monad.Unionable
open import Monad.Principal

open import MorphMonad.Types
open import MorphMonad.Diamond1
open import MorphMonad.Diamond2
open import MorphMonad.Closure

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
  ; law-id = law-id
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1
  ; lawDiamond2 = lawDiamond2
  ; law-assoc = law-assocMorph
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

    law-id : ⟨ Id ⟩ ≡ Identity
    law-id = refl
 
    lawFunctor1 : ∀ (M : TyCons) → Morph[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ (inj₁ MonadTC)) = FunctorB
    lawFunctor1 (inj₂ (inj₂ MonadTC)) = FunctorB
    
    lawFunctor2 : ∀ (M : TyCons) → (b : Morph[ M , Id ]▷ M) 
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id law-id) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ (inj₁ MonadTC)) FunctorB m = law-left-id monad₁ m
    lawFunctor2 (inj₂ (inj₂ MonadTC)) FunctorB m = law-left-id monad₂ m

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
              → (bind M Id N b₁) (f v) (id law-id) ≡ (bind Id M N b₂) (id law-id v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) () () v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) () () v f
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB ReturnB v f = pmLawMorph3 pm₁ idTC (inj₂ MonadTC) ReturnB ReturnB v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₁ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) Morph2I1B MorphI21B v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB ReturnB v f = pmLawMorph3 pm₂ idTC (inj₂ MonadTC) ReturnB ReturnB v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph1I2B MorphI12B v f = begin
      bindMorph1I2 (bindReturn monad₁) bindMorph112 (f v) (id law-id)
        ≡⟨ refl ⟩
      bindMorph112 (f v) (λ a → (bindReturn monad₁) ((id law-id) a) (id refl))
        ≡⟨ refl ⟩
      bindMorph112 (f v) (mReturn monad₁)
        ≡⟨ morphReturnIdLaw (f v) ⟩
      bindMorph112 ((mReturn monad₁) (f v)) (id refl)
        ≡⟨ refl ⟩
      bindMorph112 ((bindReturn monad₁) (f (id law-id v)) (id refl)) (id refl)
        ≡⟨ refl ⟩
      bindMorphI12 (bindReturn monad₁) bindMorph112 (id law-id v) f ∎
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₂ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f

    -- bindReturn m ma f = mReturn m (f ma)

    -- bindMorphI12 retB m112B m f = m112B (retB (f m) (id refl)) (id refl)


    -- bindMorph1I2 retB m112B m f = m112B m (λ a → retB (f a) (id refl))

    -- bindMorphI21 m2I1B m f = m2I1B (f m) (id refl)
    -- bindApply m ma f = mBind m (mReturn m ma) f

    -- law-right-id = return a >>= k ≡ k a

    -- morphReturnIdLaw = (∀ {α : Type} → (x : M₁ α) → bindMorph112 x (mReturn monad₁) ≡ bindMorph112 ((mReturn monad₁) x) (id refl))
    
    
    lawReturnSym112 : ∀ {α β} → (a : α) → (k : α → M₁ β) → bindMorph112 (mReturn monad₁ a) k ≡ bindMorph112 (k a) (mReturn monad₁)
    lawReturnSym112 = {!!}

    law-right-id2I1 : ∀ {α β} → (m : α) → (f : α → β) → bindMorph2I1 (mReturn monad₂ m) f ≡ (mReturn monad₁ (f m))
    law-right-id2I1 = {!!}
    
    law-right-id112 : ∀ {α β} → (a : α) → (f : α → β) → bindMorph112 (mReturn monad₁ a) (λ x → mReturn monad₁ (f x)) ≡ mReturn monad₂ (f a)
    law-right-id112 = {!!}

     -- TODO: monadMorph112 x (mReturn monad₁) ≡ x


    law-assocMorph : ∀ (M N P R T S : MonadMorphTyCons) 
                    (b₁ : Morph[ M , N ]▷ P) (b₂ : Morph[ P , R ]▷ T) 
                    (b₃ : Morph[ N , R ]▷ S) (b₄ : Morph[ M , S ]▷ T)
                  → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
                  → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) IdentB IdentB ReturnB () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) IdentB IdentB ReturnB () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ReturnB ReturnB ApplyB m f g =
      sym (law-right-id monad₁ m (λ x → mReturn monad₁ (g (f x))))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ReturnB ReturnB MorphI21B m f g = begin
      bindReturn monad₁ (bindId m f) g
        ≡⟨ refl ⟩
      mReturn monad₁ (g (f m)) 
        ≡⟨ sym (law-right-id2I1 (g (f m)) (id refl)) ⟩
      bindMorph2I1 (mReturn monad₂ (g (f m))) (id refl)
        ≡⟨ refl ⟩
      bindMorphI21 bindMorph2I1 m (λ x → bindReturn monad₂ (f x) g) ∎
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ReturnB ReturnB MorphI12B m f g = begin
      bindReturn monad₂ (bindId m f) g
        ≡⟨ refl ⟩
      mReturn monad₂ (g (f m))
        ≡⟨ sym (law-right-id112 (g (f m)) (id refl)) ⟩
      bindMorph112 (mReturn monad₁ (g (f m))) (mReturn monad₁)
        ≡⟨ morphReturnIdLaw (mReturn monad₁ (g (f m))) ⟩ 
      bindMorph112 (mReturn monad₁ (mReturn monad₁ (g (f m)))) (id refl)
        ≡⟨ refl ⟩
      bindMorphI12 (bindReturn monad₁) bindMorph112 m (λ x → bindReturn monad₁ (f x) g) ∎
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ReturnB ReturnB ApplyB m f g = 
      sym (law-right-id monad₂ m (λ x → mReturn monad₂ (g (f x))))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S IdentB () b3 b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S IdentB () b3 b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) IdentB b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) IdentB b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ApplyB ApplyB ApplyB m f g =
      sym (law-right-id monad₁ m ((λ x → mBind monad₁ (mReturn monad₁ (f x)) g)))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ApplyB MorphI12B MorphI21B m f g = begin
      bindApply monad₁ (bindId m f) g
        ≡⟨ refl ⟩
      mBind monad₁ (mReturn monad₁ (f m)) g
        ≡⟨ law-right-id monad₁ (f m) g ⟩
      g (f m)
        ≡⟨ {!!} ⟩
-- morphReturnIdLaw = (∀ {α : Type} → (x : M₁ α) → bindMorph112 x (mReturn monad₁) ≡ bindMorph112 ((mReturn monad₁) x) (id refl))
      bindMorph2I1 (bindMorph112 (g (f m)) (mReturn monad₁)) (id refl)
        ≡⟨ cong (λ X → bindMorph2I1 X (id refl)) (morphReturnIdLaw (g (f m))) ⟩
      bindMorph2I1 (bindMorph112 (mReturn monad₁ (g (f m))) (id refl)) (id refl)
        ≡⟨ refl ⟩
      bindMorphI21 bindMorph2I1 m (λ x → bindMorphI12 (bindReturn monad₁) bindMorph112 (f x) g) ∎
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB MorphI12B ApplyB MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB MorphI12B MorphI12B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB MorphI21B MorphI21B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB MorphI21B ApplyB MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) IdentB ApplyB MorphI21B MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) IdentB ApplyB ApplyB ApplyB m f g = 
      sym (law-right-id monad₂ m (λ x → mBind monad₂ (mReturn monad₂ (f x)) g))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 () IdentB b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 () IdentB b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g = begin
      bindFunctor monad₁ (bindReturn monad₁ m f) g
        ≡⟨ refl ⟩
      mBind monad₁ (mReturn monad₁ (f m)) (λ x → mReturn monad₁ (g x)) 
        ≡⟨ law-right-id monad₁ (f m) (λ x → mReturn monad₁ (g x)) ⟩
      mReturn monad₁ (g (f m))
        ≡⟨ refl ⟩
      bindReturn monad₁ m (λ x → bindId (f x) g) ∎
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ReturnB Morph1I2B IdentB ReturnB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ReturnB Morph2I1B IdentB ReturnB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g = 
      law-right-id monad₂ (f m) (λ x → mReturn monad₂ (g x))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB FunctorB ReturnB ApplyB m f g = 
      trans (law-right-id monad₁ (f m) (λ x → mReturn monad₁ (g x))) (sym (law-right-id monad₁ m (λ x → mReturn monad₁ (g (f x)))))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph1I2B ReturnB MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph2I1B ReturnB ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB FunctorB ReturnB MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB FunctorB ReturnB MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph1I2B ReturnB ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph2I1B ReturnB MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB FunctorB ReturnB ApplyB m f g =
      trans (law-right-id monad₂ (f m) (λ x → mReturn monad₂ (g x))) (sym (law-right-id monad₂ m (λ x → mReturn monad₂ (g (f x)))))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB MonadB ApplyB ApplyB m f g = 
      sym (law-right-id monad₁ m (λ x → mBind monad₁ (mReturn monad₁ (f x)) g))
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph112B ApplyB MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph121B MorphI21B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph122B MorphI21B MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph211B ApplyB ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph212B ApplyB MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB Morph221B MorphI21B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ReturnB MonadB MorphI21B MorphI12B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB MonadB MorphI12B MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph112B MorphI12B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph121B ApplyB MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph122B ApplyB ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph211B MorphI12B MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph212B MorphI12B ApplyB m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB Morph221B ApplyB MorphI21B m f g = {!!}
    law-assocMorph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ReturnB MonadB ApplyB ApplyB m f g = 
      sym (law-right-id monad₂ m (λ x → mBind monad₂ (mReturn monad₂ (f x)) g))
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 () IdentB m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ P) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₁ IdentTC) (inj₂ N) (inj₂ P) R (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}

    law-assocMorph (inj₂ M) N P R T S b1 b2 b3 b4 m f g = {!!} {-
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 IdentB () m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) b1 b2 IdentB () m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 IdentB b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ S) b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₁ IdentTC) (inj₂ P) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) b1 b2 b3 () m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ P) (inj₂ R) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T S () b2 b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ N) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S b1 () b3 b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ S) b1 Morph211B b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ S) b1 Morph212B b3 b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ (inj₂ MonadTC)) b1 b2 Morph122B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ (inj₁ MonadTC)) b1 b2 Morph121B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) b1 Morph211B Morph211B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) b1 Morph212B Morph211B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) b1 Morph211B Morph212B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) b1 Morph212B Morph212B b4 m f g = {!!}
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC) b1 b2 () b4 m f g
    law-assocMorph (inj₂ M) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₂ S) b1 b2 b3 b4 m f g = {!!}
   
-}
