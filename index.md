
# Index

## Structures

Structures that are listed as _Haskell_ structures are a formalization of that 
structure in the category **Set** as it is done in Haskell.

| # | Structure | Module |
|---|-----------|--------|
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
| 300 |  | |

## Relationships

An isomorphism or implication between structures listed here just indicates that there are cases where these implications 
hold, but they are not necessarily generally true.

Legend:
* A &cong; B -- Proof that A isomorphic to B.
* A &rArr; B -- Proof that A implies an instance of B. Can be interpreted as A is a subset of B.

| Rel. | Module |
|------|--------|
| 4 &cong; 202 | [`Theory.Functor.Monoidal.Properties.IsomorphicGradedApplicative`](src/Theory/Functor/Monoidal/Properties/IsomorphicGradedApplicative.agda) |







