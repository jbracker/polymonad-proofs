
# Index

## Formalizations and Examples

Formalizations that are listed as _Haskell_ structures are a formalization of that 
structure in the category **Set** reflecting the way it is encoded in Haskell.

| # | Formalization | Module |
|---|---------------|--------|
| 1 | Haskell Functor | [`Haskell.Functor`](src/Haskell/Functor.agda) |
| 2 | Haskell Applicative | [`Haskell.Applicative`](src/Haskell/Applicative.agda) |
| 3 | Haskell Monad | [`Haskell.Monad`](src/Haskell/Monad.agda) |
| 4 | Haskell Graded Applicative | [`Haskell.Parameterized.Graded.Applicative`](src/Haskell/Parameterized/Graded/Applicative.agda) |
| 5 | Haskell Graded Monad | [`Haskell.Parameterized.Graded.Monad`](src/Haskell/Parameterized/Graded/Monad.agda) |
| 6 | Haskell Indexed Applicative | [`Haskell.Parameterized.Indexed.Applicative`](src/Haskell/Parameterized/Indexed/Applicative.agda) |
| 7 | Haskell Indexed Monad | [`Haskell.Parameterized.Indexed.Monad`](src/Haskell/Parameterized/Indexed/Monad.agda) |
| 100 | Category | [`Theory.Category.Definition`](src/Theory/Category/Definition.agda) |
| 101 | Monoidal Category | [`Theory.Category.Monoidal`](src/Theory/Category/Monoidal.agda) |
| 200 | Functor | [`Theory.Functor.Definition`](src/Theory/Functor/Definition.agda) |
| 201 | Monoidal Functor | [`Theory.Functor.Monoidal`](src/Theory/Functor/Monoidal.agda) |
| 202 | Lax Monoidal Functor | [`Theory.Functor.Monoidal`](src/Theory/Functor/Monoidal.agda) |
| 203 | Graded Lax Monoidal Functor | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor.agda) |
| 204 | Indexed Lax Monoidal Functor | [`Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor`](src/Theory/Haskell/Parameterized/Indexed/LaxMonoidalFunctor.agda) |
| 300 | Monad | [`Theory.Monad.Definition`](src/Theory/Monad/Definition.agda) |
| 301 | Graded Monad | [`Theory.Haskell.Parameterized.Graded.Monad`](src/Theory/Haskell/Parameterized/Graded/Monad.agda) |
| 302 | Indexed Monad | [`Theory.Haskell.Parameterized.Indexed.Monad`](src/Theory/Haskell/Parameterized/Indexed/Monad.agda) |
| 303 | Kleisli Triple | [`Theory.Monad.Kleisli`](src/Theory/Monad/Kleisli.agda) |
| 304 | Relative Monad | [`Theory.Monad.Relative`](src/Theory/Monad/Relative.agda) |
| 305 | Atkey's Parameterized Monad | [`Theory.Monad.Atkey`](src/Theory/Monad/Atkey.agda) |
| 400 | Natural Transformation | [`Theory.Natural.Transformation`](src/Theory/Natural/Transformation.agda) |
| 401 | Natural Isomorphism | [`Theory.Natural.Isomorphism`](src/Theory/Natural/Isomorphism.agda) |
| 500 | Strict 2-Category | [`Theory.TwoCategory.Definition`](src/Theory/TwoCategory/Definition.agda) |
| 501 | Bicategory | [`Theory.TwoCategory.Bicategory`](src/Theory/TwoCategory/Bicategory.agda) |
| 600 | Lax 2-Functor (on Strict 2-Categories) | [`Theory.TwoFunctor.Definition`](src/Theory/TwoFunctor/Definition.agda) |
| 601 | Lax 2-Functor (constant 0-Cell mapping) | [`Theory.TwoFunctor.ConstZeroCell`](src/Theory/TwoFunctor/ConstZeroCell.agda) |
| 900 | Monoid | [`Theory.Monoid`](src/Theory/Monoid.agda) |

## Relationships

An isomorphism or implication between structures listed here just indicates that there are cases where these implications 
hold, but they are not necessarily generally true.

Legend:
* A &cong; B -- Proof that A isomorphic to B.
* A &rArr; B -- Proof that A implies an instance of B. Can be interpreted as A is a subset of B.

| Rel. | Module |
|------|--------|
| 001&cong;200 | [`Theory.Functor.Properties.IsomorphicHaskellFunctor`](src/Theory/Functor/Properties/IsomorphicHaskellFunctor.agda) |
| 002&cong;202 | [`Theory.Functor.Monoidal.Properties.IsomorphicHaskellApplicative`](src/Theory/Functor/Monoidal/Properties/IsomorphicHaskellApplicative.agda) |
| 003&cong;202 | [`Theory.Functor.Monoidal.Properties.IsomorphicMonad`](src/Theory/Functor/Monoidal/Properties/IsomorphicMonad.agda) |
| 003&cong;300 | [`Theory.Monad.Properties.IsomorphicHaskellMonad`](src/Theory/Monad/Properties/IsomorphicHaskellMonad.agda) |
| 004&cong;202 | [`Theory.Functor.Monoidal.Properties.IsomorphicGradedApplicative`](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedApplicative.agda) |
| 004&cong;203 | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicHaskellGradedApplicative`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicHaskellGradedApplicative.agda) |
| 005&cong;202 | [`Theory.Functor.Monoidal.Properties.IsomorphicGradedMonad`](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedMonad.agda) |
| 005&cong;301 | [`Theory.Haskell.Parameterized.Graded.Monad.Properties.IsomorphicHaskellGradedMonad`](src/Theory/Haskell/Parameterized/Graded/Monad/Properties/IsomorphicHaskellGradedMonad.agda) |
| 006&cong;204 | [`Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.IsomorphicHaskellIndexedApplicative`](src/Theory/Haskell/Parameterized/Indexed/LaxMonoidalFunctor/Properties/IsomorphicHaskellIndexedApplicative.agda) |
| 007&cong;302 | [`Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicHaskellIndexedMonad`](src/Theory/Haskell/Parameterized/Indexed/Monad/Properties/IsomorphicHaskellIndexedMonad.agda) |
| 007&cong;305 | [`Theory.Monad.Atkey.Properties.IsomorphicIndexedMonad`](src/Theory/Monad/Atkey/Properties/IsomorphicIndexedMonad.agda) |
| 200&cong;001 | [`Theory.Functor.Properties.IsomorphicHaskellFunctor`](src/Theory/Functor/Properties/IsomorphicHaskellFunctor.agda) |
| 200&rArr;600 | [`Theory.TwoFunctor.Properties.FromFunctor`](src/Theory/TwoFunctor/Properties/FromFunctor.agda) |
| 202&cong;002 | [`Theory.Functor.Monoidal.Properties.IsomorphicHaskellApplicative`](src/Theory/Functor/Monoidal/Properties/IsomorphicHaskellApplicative.agda) |
| 202&cong;003 | [`Theory.Functor.Monoidal.Properties.IsomorphicMonad`](src/Theory/Functor/Monoidal/Properties/IsomorphicMonad.agda) |
| 202&cong;004 | [`Theory.Functor.Monoidal.Properties.IsomorphicGradedApplicative`](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedApplicative.agda) |
| 202&cong;005 | [`Theory.Functor.Monoidal.Properties.IsomorphicGradedMonad`](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedMonad.agda) |
| 202&cong;203 | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicLaxMonoida`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda) |
| 202&cong;601 | [`Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor`](src/Theory/TwoFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda) |
| 203&cong;004 | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicHaskellGradedApplicative`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicHaskellGradedApplicative.agda) |
| 203&cong;202 | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.IsomorphicLaxMonoida`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda) |
| 204&cong;006 | [`Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.IsomorphicHaskellIndexedApplicative`](src/Theory/Haskell/Parameterized/Indexed/LaxMonoidalFunctor/Properties/IsomorphicHaskellIndexedApplicative.agda) |
| 300&cong;003 | [`Theory.Monad.Properties.IsomorphicHaskellMonad`](src/Theory/Monad/Properties/IsomorphicHaskellMonad.agda) |
| 300&cong;600 | [`Theory.TwoFunctor.Properties.IsomorphicMonad`](src/Theory/TwoFunctor/Properties/IsomorphicMonad.agda) |
| 301&cong;601 | [`Theory.TwoFunctor.Properties.IsomorphicGradedMonad`](src/Theory/TwoFunctor/Properties/IsomorphicGradedMonad.agda) |
| 302&cong;007 | [`Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicHaskellIndexedMonad`](src/Theory/Haskell/Parameterized/Indexed/Monad/Properties/IsomorphicHaskellIndexedMonad.agda) |
| 302&cong;601 | [`Theory.TwoFunctor.Properties.IsomorphicIndexedMonad`](src/Theory/TwoFunctor/Properties/IsomorphicIndexedMonad.agda) |
| 305&cong;007 | [`Theory.Monad.Atkey.Properties.IsomorphicIndexedMonad`](src/Theory/Monad/Atkey/Properties/IsomorphicIndexedMonad.agda) |
| 305&rArr;600 | [`Theory.TwoFunctor.Properties.FromAtkeyParameterizedMonad`](src/Theory/TwoFunctor/Properties/FromAtkeyParameterizedMonad.agda) |
| 600&cong;300 | [`Theory.TwoFunctor.Properties.IsomorphicMonad`](src/Theory/TwoFunctor/Properties/IsomorphicMonad.agda) |
| 601&cong;202 | [`Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor`](src/Theory/TwoFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda) |
| 601&cong;301 | [`Theory.TwoFunctor.Properties.IsomorphicGradedMonad`](src/Theory/TwoFunctor/Properties/IsomorphicGradedMonad.agda) |
| 601&cong;302 | [`Theory.TwoFunctor.Properties.IsomorphicIndexedMonad`](src/Theory/TwoFunctor/Properties/IsomorphicIndexedMonad.agda) |
| 601&rArr;600 | [`Theory.TwoFunctor.ConstZeroCell`](src/Theory/TwoFunctor/ConstZeroCell.agda) |


