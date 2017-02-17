 
module MorphMonad.Types where

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
open import Monad.Polymonad

-- -----------------------------------------------------------------------------
-- Bind names and type constructor names
-- -----------------------------------------------------------------------------

MonadTyCons₁ = MonadTyCons
MonadTyCons₂ = MonadTyCons

MonadBinds₁ = MonadBinds
MonadBinds₂ = MonadBinds

MonadMorphTyCons = IdTyCons ⊎ (MonadTyCons₁ ⊎ MonadTyCons₂)

mTC₁ : MonadMorphTyCons
mTC₁ = inj₂ (inj₁ MonadTC)

mTC₂ : MonadMorphTyCons
mTC₂ = inj₂ (inj₂ MonadTC)

data MonadMorphBinds : (M N P : MonadMorphTyCons) → Set where
  Morph1I2B : MonadMorphBinds mTC₁ idTC mTC₂
  MorphI12B : MonadMorphBinds idTC mTC₁ mTC₂
  Morph2I1B : MonadMorphBinds mTC₂ idTC mTC₁
  MorphI21B : MonadMorphBinds idTC mTC₂ mTC₁
  Morph112B : MonadMorphBinds mTC₁ mTC₁ mTC₂
  Morph122B : MonadMorphBinds mTC₁ mTC₂ mTC₂
  Morph211B : MonadMorphBinds mTC₂ mTC₁ mTC₁
  Morph221B : MonadMorphBinds mTC₂ mTC₂ mTC₁
  Morph212B : MonadMorphBinds mTC₂ mTC₁ mTC₂
  Morph121B : MonadMorphBinds mTC₁ mTC₂ mTC₁

Morph[_,_]▷_ : MonadMorphTyCons → MonadMorphTyCons → MonadMorphTyCons → Set
Morph[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
Morph[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ idTC idTC (inj₂ MonadTC)
Morph[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂  idTC idTC (inj₂ MonadTC)
Morph[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ idTC (inj₂ MonadTC) (inj₂ MonadTC)
Morph[ inj₁ IdentTC , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds idTC mTC₁ mTC₂
Morph[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadMorphBinds idTC mTC₂ mTC₁
Morph[ inj₁ IdentTC , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂ idTC (inj₂ MonadTC) (inj₂ MonadTC)
Morph[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ (inj₂ MonadTC) idTC (inj₂ MonadTC)
Morph[ inj₂ (inj₁ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds mTC₁ idTC mTC₂
Morph[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadBinds₁ (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)
Morph[ inj₂ (inj₁ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadMorphBinds mTC₁ mTC₁ mTC₂
Morph[ inj₂ (inj₁ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₁ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ P = MonadMorphBinds mTC₁ mTC₂ (inj₂ P)
Morph[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₁ MonadTC) = MonadMorphBinds mTC₂ idTC mTC₁
Morph[ inj₂ (inj₂ MonadTC) , inj₁ IdentTC ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₂ (inj₂ MonadTC) idTC (inj₂ MonadTC)
Morph[ inj₂ (inj₂ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₂ MonadTC) , inj₂ (inj₁ MonadTC) ]▷ inj₂ P = MonadMorphBinds mTC₂ mTC₁ (inj₂ P)
Morph[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₁ IdentTC = ⊥
Morph[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₁ MonadTC) = MonadMorphBinds mTC₂ mTC₂ mTC₁
Morph[ inj₂ (inj₂ MonadTC) , inj₂ (inj₂ MonadTC) ]▷ inj₂ (inj₂ MonadTC) = MonadBinds₁ (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)

-- -----------------------------------------------------------------------------
-- Bind operations on depending on return, morph2I1 and morph112
-- -----------------------------------------------------------------------------

bindMorph1I2 : ∀ { M P : TyCon } → [ Identity , Identity ]▷ M → [ M , M ]▷ P → [ M , Identity ]▷ P
bindMorph1I2 retB m112B m f = m112B m (λ a → retB (f a) (id refl))

bindMorphI12 : ∀ { M P : TyCon } → [ Identity , Identity ]▷ M → [ M , M ]▷ P → [ Identity , M ]▷ P
bindMorphI12 retB m112B m f = m112B (retB (f m) (id refl)) (id refl)

bindMorphI21 : ∀ {M P} → [ P , Identity ]▷ M → [ Identity , P ]▷ M
bindMorphI21 m2I1B m f = m2I1B (f m) (id refl)

bindMorph122 : ∀ {M P} → [ P , Identity ]▷ M → [ M , M ]▷ P → [ M , P ]▷ P
bindMorph122 m2I1B m112B m f = m112B m (λ z → m2I1B (f z) (id refl))

bindMorph211 : ∀ {M P} → [ P , Identity ]▷ M → [ M , M ]▷ P → [ P , M ]▷ M
bindMorph211 m2I1B m112B m f = m2I1B (m112B (m2I1B m f) (id refl)) (id refl)

bindMorph221 : ∀ {M P} → [ P , Identity ]▷ M → [ M , M ]▷ P → [ P , P ]▷ M
bindMorph221 m2I1B m112B m f = m2I1B (m112B (m2I1B m (λ z → m2I1B (f z) (id refl))) (id refl)) (id refl)

bindMorph121 : ∀ {M P} → [ P , Identity ]▷ M → [ M , M ]▷ P → [ M , P ]▷ M
bindMorph121 m2I1B m112B m f = m2I1B (m112B m (λ z → m2I1B (f z) (id refl))) (id refl)

bindMorph212 : ∀ {M P} → [ P , Identity ]▷ M → [ M , M ]▷ P → [ P , M ]▷ P
bindMorph212 m2I1B m112B m f = m112B (m2I1B m f) (id refl)
