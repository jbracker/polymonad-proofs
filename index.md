
# Index

## Formalizations and Examples

Formalizations that are listed as _Haskell_ structures are a formalization of that 
structure in the category **Set** reflecting the way it is encoded in Haskell.

| Formalization | Module |
|---------------|--------|
| Haskell Functor | [`Haskell.Functor`](src/Haskell/Functor.agda) |
| Haskell Applicative | [`Haskell.Applicative`](src/Haskell/Applicative.agda) |
| Haskell Monad | [`Haskell.Monad`](src/Haskell/Monad.agda) |
| Haskell Graded Applicative | [`Haskell.Parameterized.Graded.Applicative`](src/Haskell/Parameterized/Graded/Applicative.agda) |
| Haskell Graded Monad | [`Haskell.Parameterized.Graded.Monad`](src/Haskell/Parameterized/Graded/Monad.agda) |
| Haskell Indexed Applicative | [`Haskell.Parameterized.Indexed.Applicative`](src/Haskell/Parameterized/Indexed/Applicative.agda) |
| Haskell Indexed Monad | [`Haskell.Parameterized.Indexed.Monad`](src/Haskell/Parameterized/Indexed/Monad.agda) |
| Category | [`Theory.Category.Definition`](src/Theory/Category/Definition.agda) |
| Monoidal Category | [`Theory.Category.Monoidal`](src/Theory/Category/Monoidal.agda) |
| Functor | [`Theory.Functor.Definition`](src/Theory/Functor/Definition.agda) |
| Monoidal Functor | [`Theory.Functor.Monoidal`](src/Theory/Functor/Monoidal.agda) |
| Lax Monoidal Functor | [`Theory.Functor.Monoidal`](src/Theory/Functor/Monoidal.agda) |
| Graded Lax Monoidal Functor | [`Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor`](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor.agda) |
| Indexed Lax Monoidal Functor | [`Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor`](src/Theory/Haskell/Parameterized/Indexed/LaxMonoidalFunctor.agda) |
| Monad | [`Theory.Monad.Definition`](src/Theory/Monad/Definition.agda) |
| Graded Monad | [`Theory.Haskell.Parameterized.Graded.Monad`](src/Theory/Haskell/Parameterized/Graded/Monad.agda) |
| Indexed Monad | [`Theory.Haskell.Parameterized.Indexed.Monad`](src/Theory/Haskell/Parameterized/Indexed/Monad.agda) |
| Kleisli Triple | [`Theory.Monad.Kleisli`](src/Theory/Monad/Kleisli.agda) |
| Relative Monad | [`Theory.Monad.Relative`](src/Theory/Monad/Relative.agda) |
| Atkey's Parameterized Monad | [`Theory.Monad.Atkey`](src/Theory/Monad/Atkey.agda) |
| Natural Transformation | [`Theory.Natural.Transformation`](src/Theory/Natural/Transformation.agda) |
| Natural Isomorphism | [`Theory.Natural.Isomorphism`](src/Theory/Natural/Isomorphism.agda) |
| Strict 2-Category | [`Theory.TwoCategory.Definition`](src/Theory/TwoCategory/Definition.agda) |
| Bicategory | [`Theory.TwoCategory.Bicategory`](src/Theory/TwoCategory/Bicategory.agda) |
| Lax 2-Functor (on Strict 2-Categories) | [`Theory.TwoFunctor.Definition`](src/Theory/TwoFunctor/Definition.agda) |
| Lax 2-Functor (constant 0-Cell mapping) | [`Theory.TwoFunctor.ConstZeroCell`](src/Theory/TwoFunctor/ConstZeroCell.agda) |
| Monoid | [`Theory.Monoid`](src/Theory/Monoid.agda) |

## Relationships

An isomorphism or implication between structures listed here just indicates that there are cases where these implications 
hold, but they are not necessarily generally true.

Legend:
* A &cong; B -- Proof that A isomorphic to B.
* A &rArr; B -- Proof that A implies an instance of B. Can be interpreted as A is a subset of B.

Index:
* [Atkey's Parameterized Monad &rArr; Lax 2-Functor](src/Theory/TwoFunctor/Properties/FromAtkeyParameterizedMonad.agda)
* [Atkey's Parameterized Monad &cong; Haskell Indexed Monad](src/Theory/Monad/Atkey/Properties/IsomorphicIndexedMonad.agda)
* [Functor &cong; Haskell Functor](src/Theory/Functor/Properties/IsomorphicHaskellFunctor.agda)
* [Functor &rArr; Lax 2-Functor](src/Theory/TwoFunctor/Properties/FromFunctor.agda)
* [Graded Lax Monoidal Functor &cong; Haskell Graded Applicative](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicHaskellGradedApplicative.agda)
* [Graded Monad &cong; Haskell Graded Monad](src/Theory/Haskell/Parameterized/Graded/Monad/Properties/IsomorphicHaskellGradedMonad.agda)
* [Graded Monad &cong; Lax 2-Functor](src/Theory/TwoFunctor/Properties/IsomorphicGradedMonad.agda)
* [Indexed Lax Monoidal Functor &cong; Haskell Indexed Applicative](src/Theory/Haskell/Parameterized/Indexed/LaxMonoidalFunctor/Properties/IsomorphicHaskellIndexedApplicative.agda)
* [Indexed Monad &cong; Haskell Indexed Monad](src/Theory/Haskell/Parameterized/Indexed/Monad/Properties/IsomorphicHaskellIndexedMonad.agda)
* [Indexed Monad &cong; Lax 2-Functor](src/Theory/TwoFunctor/Properties/IsomorphicIndexedMonad.agda)
* [Indexed Monad &cong; Graded Monad](src/Theory/Haskell/Parameterized/Indexed/Monad/Properties/IsomorphicGradedMonad.agda)
* [Lax Monoidal Functor &cong; Graded Lax Monoidal Functor](src/Theory/Haskell/Parameterized/Graded/LaxMonoidalFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda)
* [Lax Monoidal Functor &cong; Indexed Lax Monoidal Functor](src/Theory.Haskell/Parameterized/Indexed/LaxMonoidalFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda)
* [Lax Monoidal Functor &cong; Graded Monad](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedMonad.agda)
* [Lax Monoidal Functor &cong; Monad](src/Theory/Functor/Monoidal/Properties/IsomorphicMonad.agda)
* [Lax Monoidal Functor &cong; Haskell Applicative](src/Theory/Functor/Monoidal/Properties/IsomorphicHaskellApplicative.agda)
* [Lax Monoidal Functor &cong; Haskell Graded Applicative](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedApplicative.agda)
* [Lax Monoidal Functor &cong; Haskell Graded Monad](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedMonad.agda)
* [Lax Monoidal Functor &cong; Lax 2-Functor](src/Theory/TwoFunctor/Properties/IsomorphicLaxMonoidalFunctor.agda)
* [Monad &cong; Haskell Monad](src/Theory/Monad/Properties/IsomorphicHaskellMonad.agda)
* [Monad &cong; Lax 2-Functor](src/Theory/TwoFunctor/Properties/IsomorphicMonad.agda)

