 
# Formalizations and Proofs of Category Theory, Supermonads and Polymonads 

This repository contains the formalization of supermonads [(Bracker and Nilsson, 2016)](http://www.cs.nott.ac.uk/~psxjb5/publications/2016-BrackerNilsson-Supermonads.pdf) 
and polymonads [(Hicks et al., 2014)](http://www.cs.bham.ac.uk/~pbl/msfp2014/polymonad.pdf)
as well as formalizations and proofs about their connection to category theory.

The connection between the categorical notions and Haskell is hinted at
by proof of equivalency between Haskell-like notions in the category *Set*
and their categorical counterparts.

## Type Checking and Versions

Calling `make` should type check all files that don't contain 
unsolved holes.

This was tested with Agda in version `2.5.3` and the Adga standard library 
in version `0.14`. If you have problems type checking the code, please contact
me.

Type checking some of the proofs, e.g., `Polymonad.Union`, is very memory hungry. 
Make sure you have few gigabytes of free RAM when type checking!

## Module Structure and Guide

* **Top-level Modules**:
  * `Identity`:
    Contains some basic stuff about the identity and the identity type function.
    Provides an identity Kleisli-arrow that is polymorphic over the identity type
    constructor; this is central to the formalization of polymonads.
  * `Utilities`:
    Basic stuff to formalize things and provides utilities that
    are used throughout.
  * `Extensionality`:
    We postulate function extensionality here and make extensive use of it accross all
    modules. This modules contains helper to utilize function extensionality
    in the context of heterogeneous equality and implicit arguments.
  * `Equality`:
    Helpers to prove equality of library data structures.
  * `Congruence`:
    Generalization of congruence for propositional equality up to nine arguments.
    Usefulness is limited.
  * `Substitution`:
    Generalization of substitution for propositional equality up to nine arguments.
    Usefulness is limited.
  * `Bijection`:
    Definition of what it means for a function to be bijective. 
    These definitions are mainly used to prove that structures are
    isomorphic in the `Theory` modules.
  * `ProofIrrelevance`:
    Proofs of proof irrelevance for several library data types.
  * `Haskell`:
    Collection of basic definitions and utilities in the category *Set*.
* **`Haskell`**:
  Formalizations of Haskell-like structures in the category *Set*.
  * **`Functor`**:
    Formalization of functors as they are represented in Haskell
    together with a derivation from a monad.
  * **`Applicative`**:
    Formalization of applicative functor as they are represented in Haskell
    together with a derivation from a monad.
  * **`Monad`**:
    Formalization of monads as they are represented in Haskell.
    * `Polymonad`, `Unionable` and `Principal`:
      Monads form polymonads, are unionable, and principal.
    * `PrincipalUnion`:
      A specialised proof that the union of monads forms a principal polymonad.
    * `Identity`, `List` and `Maybe`:
      The `Identity`, `List`, and `Maybe` monad.
  * **`Parameterized`**:
    Formalizations of graded and indexed monads as they are represented in Haskell.
    * `Indexed`: 
      Formalization of indexed monads and applicatives. Contains proof that 
      they are polymonads and the applicative notion can be derived from the monadic notion.
    * `Graded`:
      Formalization of graded monads and applicatives. Contains proof that 
      they are polymonads and the applicative notion can be derived from the monadic notion.
* **`Hicks`**:
  Contains a formalization of Hicks polymonads without the alteration. 
  * `Equivalency` shows that both formulations are equivalent.
  * `UniqueBinds` shows that bind-operations are unique in this formalization of polymonads as well.
* **`Polymonad`**:
  Formalization of polymonads (slightly altered from the version in Hicks paper).
  The submodules contain proofs and formalizations of other polymonad concepts.
  * `Identity`: 
    The identity polymonad.
  * `Unionable`: 
    The formalization of what is required to 
    union two polymonads that do not have morphisms between them.
  * `Union`: 
    The proof that `UnionablePolymonad`s actually form a polymonad again.
  * `Union.Principal`: 
    Proof that union preserves principality (under some preconditions).
  * `Principal`: 
    The formalization of principal polymonads.
  * `UniqueBinds`: 
    Proof that bind-operations on the same type 
    are unique, i.e., bind-operations with the same type have the same semantics.
* **`MorphMonad`**: 
  These modules contain ideas about the union of standard monads to polymonads by providing lifting
  functions (morphisms) between them (discontinued).
* **`Supermonad`**:
  Another approach to generalizing different kinds of monads, that we call Supermonads. 
  This approach is driven by practical examples of generalized monads. This is a formalization
  of supermonads based on the definition given in 
  the supermonad paper [(Bracker and Nilsson, 2016)](http://www.cs.nott.ac.uk/~psxjb5/publications/2016-BrackerNilsson-Supermonads.pdf).
  * `EffectMonad`, `IxMonad` and `Monad`:
    Examples of how standard, graded and effect monads can be made supermonads according to this 
    formalization.
* **`Theory`**:
  Formalization of category theory to give a category theoretic model of supermonads.
  * `Monoid` and `Triple`:
    Definition of monoids and triples.
  * **`Category`**:
    Definition of categories, subcategories, monoidal categories and closed categories.
    * `Examples` and `Monoidal.Examples`:
      Examples for categories and monoidal categories, e.g., Set,
      categories of functor and natural transformations, monoid and (co)discrete categories.
    * `Dependent` and `Monoidal.Dependent`:
      Definition of product categories using dependent products.
    * `Isomorphism`:
      Definition of what it means for a morphism in a category to be an isomorphism.
      This definition is equivalent to the definition in the `Bijection` module
      when the underlying category is *Set*.
  * **`Functor`**:
    Definition of functors, profunctors, (lax) monoidal functors and closed functors.
    * `Application`, `Association`, `Constant` and `Composition`:
      Combinators to manipulate functors, e.g., apply them to certain arguments, compose them or reassociate them.
    * `Examples`:
      Some examples of functors.
    * `Properties.IsomorphicHaskellFunctor`:
      Proof that functors in Haskell (*Set*) are isomorphic to categorical functors.
    * `Monoidal.Properties.IsomorphicHaskellApplicative`:
      Proof that applicative functors in Haskell (*Set*) are isomorhic to certain lax monoidal functors.
    * `Monoidal.Properties.IsomorphicGradedApplicative`:
      Proof that graded applicative functors in Haskell (*Set*) are isomorhic to certain lax monoidal functors.
    * `Monoidal.Properties.IsomorphicMonad`:
      Proof that monads in Haskell (*Set*) are isomorhic to certain lax monoidal functors.
    * `Monoidal.Properties.IsomorphicGradedMonad`:
      Proof that graded monads in Haskell (*Set*) are isomorhic to certain lax monoidal functors.
  * **`Natural`**:
    Definition of (di/extra)natural transformations and isomorphisms.
    * `Transformation.Examples` and `Isomorphism.Examples`:
      Examples of natural transformations and isomorphism.
  * **`Monad`**:
    Definition of different monadic notions.
    * `Definition`: Definition of standard categorical monads.
    * `Kleisli`: Definition of monads as Kleisli triples, together with proof of conversion between monads and kleisli triples.
    * `Relative`: Definition of relative monads [(Altenkirch et al., 2015)](http://www.cs.nott.ac.uk/~psztxa/publ/Relative_Monads.pdf)
    * `Atkey`: Definition of indexed monads in category theory as suggested by Atkey [(Atkey, 2009)](https://bentnib.org/paramnotions-jfp.pdf)
    * `Properties.IsomorphicHaskellMonad`:
      Proof that monads in Haskell (*Set*) are isomorhic to categorical monads.
  * **`Haskell`**:
    Categorized definitionso of Haskell concepts.
    * `Parameterized.Graded`:
      Category theory version of graded monads that is isomorphic to Haskell (*Set*) 
      graded monads if *Set* is used as the underlying category.
    * `Parameterized.Indexed`:
      Category theory version of indexed monads that is isomorphic to Haskell (*Set*) 
      indexed monads if *Set* is used as the underlying category.
    * `Constrained`:
      Specialized definition for constrained functors and applicative functors, together with an example 
      of how endomorphism and `Set`s (as in Haskell finite unordered collection without duplicates) can 
      form constrained functors.
  * **`TwoCategory`**:
    Definition of strict 2-categories and bicategories. Examples can be found in the `Examples` submodules.
  * **`TwoFunctor`**:
    Definition of lax 2-functors.
    * `ConstZeroCell`:
      A specialized definition of lax 2-functor that uses a constant mapping of 0-cells to ease some of the proofs.
      This definition yields a lax 2-functor and therefore captures a subset of all lax 2-functors.
    * `Properties`:
      * `IsomorphicMonad`: 
        Proof that certain lax 2-functors are isomorphic to categorical monads.
      * `IsomorphicGradedMonad`: 
        Proof that certain lax 2-functors are isomorphic to our definition of categorical graded monads.
      * `IsomorphicIndexedMonad`:
        Proof that certain lax 2-functors are isomorphic to our definition of categorical indexed monads.
      * `IsomorphicLaxMonoidalFunctor`:
        Proof that certain lax 2-functors are isomorphic to certain lax monoidal functors.
  * **`End`**:
    Definition of ends, wedges and day convolution. This is unfinished and discontinued work due to the 
    difficulty to capture these notions in Agda.
  * **`Yoneda`**: Proof of the Yoneda lemma.



















