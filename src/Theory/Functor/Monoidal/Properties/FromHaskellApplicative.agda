
open import Level


open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative

open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Monoidal

open import Theory.Functor.Properties.IsomorphicHaskellFunctor

module Theory.Functor.Monoidal.Properties.FromHaskellApplicative where


HaskellApplicative→LaxMonoidalFunctor
  : {F : TyCon}
  → Applicative F
  → LaxMonoidalFunctor (setMonoidalCategory {zero}) (setMonoidalCategory {zero})
HaskellApplicative→LaxMonoidalFunctor {F} applic = laxMonoidalFunctor functor {!!} {!!} {!!} {!!} {!!}
  where
    functor : Functor Hask Hask
    functor = HaskellFunctor→Functor (Applicative.functor applic)
