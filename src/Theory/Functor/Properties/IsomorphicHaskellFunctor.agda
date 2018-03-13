
module Theory.Functor.Properties.IsomorphicHaskellFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )

open import Data.Product

open import Relation.Binary.PropositionalEquality

-- Local
open import Bijection hiding ( refl )
open import Haskell
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Functor.Definition

Functor→HaskellFunctor : (F : Functor (Hask {lzero}) (Hask {lzero}))
                       → HaskellFunctor ([ F ]₀)
Functor→HaskellFunctor F = record 
  { fmap = λ f ma → [ F ]₁ f ma
  ; law-id = Functor.id F
  ; law-compose = λ f g → Functor.compose F
  }
 
HaskellFunctor→Functor : {F : TyCon} → HaskellFunctor F
                       → Functor (Hask {lzero}) (Hask {lzero})
HaskellFunctor→Functor {F} func = functor F (HaskellFunctor.fmap func) (HaskellFunctor.law-id func) (λ {a} {b} {c} {f} {g} → HaskellFunctor.law-compose func g f)


Functor↔HaskellFunctor : Functor (Hask {lzero}) (Hask {lzero}) ↔ (Σ TyCon HaskellFunctor)
Functor↔HaskellFunctor = bijection (λ F → [ F ]₀ , Functor→HaskellFunctor F)
                                   (λ F → HaskellFunctor→Functor (proj₂ F))
                                   (λ _ → refl) (λ _ → refl)

HaskellFunctor↔Functor : (Σ TyCon HaskellFunctor) ↔ Functor (Hask {lzero}) (Hask {lzero})
HaskellFunctor↔Functor = Bijection.sym Functor↔HaskellFunctor
