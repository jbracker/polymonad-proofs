
module Theory.Examples.FunctorToHaskellFunctor where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )

-- Local
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Functor
open import Theory.Examples.Category 

Functor→HaskellFunctor : (F : Functor (setCategory {lzero}) (setCategory {lzero}))
                       → HaskellFunctor ([ F ]₀)
Functor→HaskellFunctor F = record 
  { fmap = λ f ma → [ F ]₁ f ma
  ; law-id = Functor.id F
  ; law-compose = λ f g → Functor.compose F
  }
