 
module Polymonad.MaybeList where

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
open import Monad.Maybe
open import Monad.List
open import Monad.Polymonad
open import Monad.Composable
open import Monad.Principal

-- -----------------------------------------------------------------------------
-- Maybe Polymonad
-- -----------------------------------------------------------------------------

MaybeTyCons = MonadTyCons
MaybeBinds  = MonadBinds

polymonadMaybe : Polymonad (IdTyCons ⊎ MaybeTyCons) idTC
polymonadMaybe = Monad→Polymonad monadMaybe

composablePolymonadMaybe : ComposablePolymonad polymonadMaybe
composablePolymonadMaybe = Monad→ComposablePolymonad monadMaybe

principalPolymonadMaybe : PrincipalPM polymonadMaybe
principalPolymonadMaybe = Monad→PrincipalPolymonad monadMaybe

-- -----------------------------------------------------------------------------
-- List Polymonad
-- -----------------------------------------------------------------------------

ListTyCons = MonadTyCons
ListBinds  = MonadBinds

polymonadList : Polymonad (IdTyCons ⊎ ListTyCons) idTC
polymonadList = Monad→Polymonad monadList

composablePolymonadList : ComposablePolymonad polymonadList
composablePolymonadList = Monad→ComposablePolymonad monadList

principalPolymonadList : PrincipalPM polymonadList
principalPolymonadList = Monad→PrincipalPolymonad monadList

-- -----------------------------------------------------------------------------
-- MaybeList Polymonad
-- -----------------------------------------------------------------------------

MonadMorphTyCons = IdTyCons ⊎ (MaybeTyCons ⊎ ListTyCons)

mTC₁ : MonadMorphTyCons
mTC₁ = inj₂ (inj₁ MonadTC)

mTC₂ : MonadMorphTyCons
mTC₂ = inj₂ (inj₂ MonadTC)

data MonadMorphBinds : (M N P : MonadMorphTyCons) → Set where
  MorphFunctorB : MonadMorphBinds mTC₁ idTC mTC₂
  MorphApplyB : MonadMorphBinds idTC mTC₁ mTC₂
  Morph112B : MonadMorphBinds mTC₁ mTC₁ mTC₂
  Morph122B : MonadMorphBinds mTC₁ mTC₂ mTC₂

open Monad.Monad

bindMaybeListMorph : [ Maybe , Identity ]▷ List
bindMaybeListMorph (Just x) f = return monadList (f x)
bindMaybeListMorph Nothing f = Nil 

bindMaybeListApply : [ Identity , Maybe ]▷ List
bindMaybeListApply m f with f m 
bindMaybeListApply m f | Just x = return monadList x
bindMaybeListApply m f | Nothing = Nil

polymonadMaybeList : ∀ { M₁ M₂ : TyCon } 
                   → Monad M₁
                   → Monad M₂
                   → (functorMorph : [ M₁ , Identity ]▷ M₂)
                   → (applyMorph : [ Identity , M₁ ]▷ M₂)
                   → (morph112 : [ M₁ , M₁ ]▷ M₂)
                   → (morph122 : [ M₁ , M₂ ]▷ M₂)
                   → (∀ {α β : Type} (v : α) (f : α → M₁ β) → functorMorph (f v) (id refl) ≡ applyMorph (id refl v) f)
                   → Polymonad (IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)) idTC
polymonadMaybeList {M₁ = M₁} {M₂ = M₂} monad₁ monad₂ functorMorph applyMorph morph112 morph122 crossLawMorph3 = record
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = {!!} --λ {m} {n} {p} b → bind m n p b
  ; lawId = {!!} --lawId
  ; lawFunctor = {!!} --lawFunctor
  ; lawMorph1 = {!!} --lawMorph1 
  ; lawMorph2 = {!!} --lawMorph2
  ; lawMorph3 = {!!} --lawMorph3
  ; lawDiamond1 = {!!} --lawDiamond1 
  ; lawDiamond2 = {!!} --lawDiamond2
  ; lawAssoc = {!!} --lawAssoc
  ; lawClosure = {!!} --lawClosure
  } where
    TyCons = IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)

    MonadBinds₁ = MonadBinds
    MonadBinds₂ = MonadBinds

    pm₁ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₁ = Monad→Polymonad monad₁
    
    pm₂ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₂ = Monad→Polymonad monad₂
    
    Id = idTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ (inj₁ MonadTC)) = M₁
    ⟨_⟩ (inj₂ (inj₂ MonadTC)) = M₂
    
    B[_,_]▷_ : TyCons → TyCons → TyCons → Set
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ idTC idTC (inj₂ MonadTC)
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂  idTC idTC (inj₂ MonadTC)
    B[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ idTC (inj₂ MonadTC) (inj₂ MonadTC)
    B[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds idTC mTC₁ mTC₂
    B[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = ⊥
    B[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂ idTC (inj₂ MonadTC) (inj₂ MonadTC)
    B[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ (inj₂ MonadTC) idTC (inj₂ MonadTC)
    B[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds mTC₁ idTC mTC₂
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds mTC₁ mTC₁ mTC₂
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = ⊥
    B[ inj₂ (inj₁ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds mTC₁ mTC₂ mTC₂
    B[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂ (inj₂ MonadTC) idTC (inj₂ MonadTC)
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = ⊥
    B[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₁ (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)
  
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB = bindReturn monad₁
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB = bindReturn monad₂
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ApplyB = bindApply monad₁
    bind (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyMorphB = applyMorph
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    bind (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyB = bindApply monad₂
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) FunctorB = bindFunctor monad₁
    bind (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) FunctorMorphB = functorMorph
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) MonadB = bindMonad monad₁
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph112B = morph112
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    bind (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) Morph122B = morph122
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) FunctorB = bindFunctor monad₂
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    bind (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) MonadB = bindMonad monad₂

    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
 
    lawFunctor : ∀ (M : TyCons) → ∃ λ(b : B[ M , Id ]▷ M) 
               → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor (inj₁ IdentTC) = IdentB , (λ {α} m → refl)
    lawFunctor (inj₂ (inj₁ MonadTC)) = FunctorB , proj₂ (pmLawFunctor pm₁ (inj₂ MonadTC))
    lawFunctor (inj₂ (inj₂ MonadTC)) = FunctorB , proj₂ (pmLawFunctor pm₂ (inj₂ MonadTC))
    
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB = ReturnB
    lawMorph1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB = ReturnB
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) FunctorB = ApplyB
    lawMorph1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) MorphFunctorB = MorphApplyB
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    lawMorph1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorB = ApplyB

    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB = ReturnB
    lawMorph2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB = ReturnB
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) ApplyB = FunctorB
    lawMorph2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) MorphApplyB = MorphFunctorB
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) ()
    lawMorph2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) ApplyB = FunctorB

    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) (id lawId v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) ReturnB ReturnB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) ReturnB ReturnB v f = refl
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) () b₂ v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₁ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f
    lawMorph3 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorMorphB ApplyMorphB v f = crossLawMorph3 v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) () b₂ v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) () b₂ v f
    lawMorph3 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) FunctorB ApplyB v f = pmLawMorph3 pm₂ (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f

    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ApplyMorphB) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyMorphB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ApplyB) = inj₂ (inj₂ MonadTC) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , FunctorB) = inj₁ IdentTC , IdentB , FunctorB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , MonadB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MorphFunctorB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MorphFunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MorphApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphFunctorB)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MorphFunctorB) = inj₁ IdentTC , IdentB , MorphFunctorB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MorphFunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphFunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphFunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphFunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphFunctorB)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph112B) = inj₂ (inj₁ MonadTC) , ApplyB , MorphApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , MorphApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph112B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph122B) = inj₂ (inj₂ MonadTC) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph122B) = inj₂ (inj₂ MonadTC) , Morph122B , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph122B) = inj₂ (inj₂ MonadTC) , ApplyB , Morph122B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph122B) = inj₂ (inj₂ MonadTC) , Morph122B , Morph122B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphApplyB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MorphApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , FunctorB) = inj₂ (inj₂ MonadTC) , FunctorB , ApplyB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphFunctorB , FunctorB) = inj₁ IdentTC , IdentB , MorphFunctorB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , FunctorB) = inj₂ (inj₂ MonadTC) , FunctorB , Morph122B
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , FunctorB) = inj₁ IdentTC , IdentB , FunctorB
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , () , FunctorB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , FunctorB) = inj₂ (inj₂ MonadTC) , FunctorB , MonadB
    lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , MonadB) = inj₂ (inj₂ MonadTC) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphApplyB , MonadB) = inj₂ (inj₂ MonadTC) , Morph122B , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , MonadB) = inj₂ (inj₂ MonadTC) , MonadB , ApplyB
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphFunctorB , MonadB) = inj₂ (inj₂ MonadTC) , ApplyB , Morph122B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , MonadB) = inj₂ (inj₂ MonadTC) , Morph122B , Morph122B
    lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , MonadB) = inj₂ (inj₂ MonadTC) , MonadB , Morph122B
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , MonadB) = inj₂ (inj₂ MonadTC) , ApplyB , MonadB
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , () , MonadB)
    lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , MonadB) = inj₂ (inj₂ MonadTC) , MonadB , MonadB

    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , FunctorB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , MorphFunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MorphFunctorB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ (inj₂ MonadTC) , FunctorB , FunctorB
    lawDiamond2 M (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , FunctorB , FunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , FunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , MonadB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) N R (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MorphApplyB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MorphApplyB) = inj₁ IdentTC , IdentB , MorphApplyB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MorphApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , MorphFunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MorphApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , MorphApplyB)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph112B) = inj₂ (inj₁ MonadTC) , FunctorB , MorphFunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph112B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , Morph112B)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , MorphFunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , Morph112B)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , Morph112B)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , Morph112B)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , () , Morph112B)
    lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphApplyB , ApplyB) = inj₁ IdentTC , IdentB , MorphApplyB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphFunctorB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , MorphFunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph122B
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , ApplyB) = inj₂ (inj₂ MonadTC) , ApplyB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , () , ApplyB)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , ApplyB) = inj₂ (inj₂ MonadTC) , ApplyB , MonadB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , MorphFunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphApplyB , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph122B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphFunctorB , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , MorphFunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , Morph122B
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph122B) = inj₂ (inj₂ MonadTC) , Morph122B , FunctorB
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , () , Morph122B)
    lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph122B) = inj₂ (inj₂ MonadTC) , Morph122B , MonadB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , MonadB) = inj₂ (inj₂ MonadTC) , FunctorB , FunctorB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphApplyB , MonadB) = {!!}
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , MonadB) = inj₂ (inj₂ MonadTC) , FunctorB , MonadB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphFunctorB , MonadB) = {!!}
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , MonadB) = {!!}
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , MonadB) = {!!}
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , MonadB) = inj₂ (inj₂ MonadTC) , MonadB , FunctorB
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , () , MonadB)
    lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , MonadB) = inj₂ (inj₂ MonadTC) , MonadB , MonadB
{-
    lawIdRF : ∀ {M : TyCon} 
            → (monad : Monad M) 
            → ∀ {α β γ : Type} 
            → (f : α → β) → (k : β → M γ) 
            → (λ x → mBind monad (mReturn monad (f x)) k) ≡ (λ x → k (f x))
    lawIdRF monad f k = funExt (λ x → mLawIdR monad (f x) k)
    
    lawAssoc : ∀ (M N P R T S : TyCons) 
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB () () IdentB m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ MonadTC) IdentB b₂ b₃ () m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) IdentB ApplyB () ReturnB m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) IdentB ReturnB ReturnB ApplyB m f g = begin
      bindReturn monad (bindId m f) g 
        ≡⟨ refl ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (mLawIdR monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) IdentB ApplyB ApplyB ApplyB m f g = begin
      bindApply monad (bindId m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (mLawIdR monad m (λ x → mBind monad (mReturn monad (f x)) g)) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc (inj₂ MonadTC) N (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc M N (inj₂ MonadTC) R (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g = begin
      bindFunctor monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn  monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ mLawIdR monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ refl ⟩
      bindReturn monad m (λ x → bindId (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) FunctorB FunctorB IdentB FunctorB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ a → mBind monad (mReturn monad (f a)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (lawIdRF monad f (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ a → mReturn monad (g (f a)))
        ≡⟨ refl ⟩
      bindFunctor monad m (λ x → bindId (f x) g) ∎
    lawAssoc M (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc M (inj₂ MonadTC) (inj₂ MonadTC) R (inj₂ MonadTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) ReturnB FunctorB ReturnB ApplyB m f g = begin
      bindFunctor monad (bindReturn monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ mLawIdR monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (mLawIdR monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) ApplyB FunctorB FunctorB ApplyB m f g = begin
      bindFunctor monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) (λ a → mReturn monad (g a)) 
        ≡⟨ cong (λ x → mBind monad x (λ a → mReturn monad (g a)) ) (mLawIdR monad m f) ⟩
      mBind monad (f m) (λ a → mReturn monad (g a))
        ≡⟨ sym (mLawIdR monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindFunctor monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) ReturnB MonadB ApplyB ApplyB m f g = begin
      bindMonad monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (mLawIdR monad m ((λ x → mBind monad (mReturn monad (f x)) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) ApplyB MonadB MonadB ApplyB m f g = begin
      bindMonad monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) g 
        ≡⟨ cong (λ x → mBind monad x g) (mLawIdR monad m f) ⟩
      mBind monad (f m) g
        ≡⟨ sym (mLawIdR monad m ((λ x → mBind monad (f x) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindMonad monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) FunctorB FunctorB ReturnB MonadB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (funExt (λ x → mLawIdR monad (f x) ((λ a → mReturn monad (g a))))) ⟩
      mBind monad m (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) MonadB FunctorB FunctorB MonadB m f g = begin
      bindFunctor monad (bindMonad monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m f) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m f ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindFunctor monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) FunctorB MonadB ApplyB MonadB m f g = begin
      bindMonad monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) g 
        ≡⟨ sym (mLawAssoc monad m ((λ a → mReturn monad (f a))) g) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) MonadB MonadB MonadB MonadB m f g = begin
      bindMonad monad (bindMonad monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m f) g
        ≡⟨ sym (mLawAssoc monad m f g) ⟩
      mBind monad m (λ x → mBind monad (f x) g)
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindMonad monad (f x) g) ∎

    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB ) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (IdentB , IdentB , IdentB , ReturnB ) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (ReturnB , IdentB , IdentB , ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) P (inj₁ IdentTC) (inj₂ MonadTC) U (b₁ , IdentB , () , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) T U (() , IdentB , b₃ , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) T (inj₁ IdentTC) (ApplyB , IdentB , b₃ , ())
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (ApplyB , IdentB , ReturnB  , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₁ IdentTC) N P (inj₂ MonadTC) T U (b₁ , () , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) S (inj₁ IdentTC) U (() , b₂ , IdentB , b₄)
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) S (inj₁ IdentTC) (inj₁ IdentTC) (FunctorB , b₂ , IdentB , ())
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (FunctorB , ReturnB  , IdentB , FunctorB) = ReturnB
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) P S (inj₂ MonadTC) U (b₁ , b₂ , () , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) S T (inj₁ IdentTC) (() , b₂ , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , ())
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) S T (inj₂ MonadTC) (() , b₂ , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (MonadB , ReturnB  , ReturnB  , FunctorB) = ReturnB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (MonadB , FunctorB , ReturnB  , FunctorB) = FunctorB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (MonadB , ReturnB  , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (MonadB , FunctorB , FunctorB , FunctorB) = MonadB
-}
