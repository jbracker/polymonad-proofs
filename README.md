 
# Formalizations and Proofs of Category Theory, Supermonads and Polymonads 

This repository contains the formalization of supermonads [(Bracker and Nilsson 2016)](http://www.cs.nott.ac.uk/~psxjb5/publications/2016-BrackerNilsson-Supermonads.pdf) 
and polymonads [(Hicks et al. 2014)](http://www.cs.bham.ac.uk/~pbl/msfp2014/polymonad.pdf)
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

* **`Utilities`**:
  Basic stuff to formalize things and provides utilities that
  are used throughout. Function extensionality is formalized here.
* **`Haskell`**:
  All formalizations and proofs based on Haskells definitions and world.
  * **`Monad`**:
    Formalization of monads as they are represented in Haskell.
    * `Monad.Polymonad`, `Monad.Unionable` and `Monad.Principal`:
      Monads form polymonads, are unionable, and principal.
    * `Monad.PrincipalUnion`:
      A specialised proof that the union of monads forms a principal polymonad.
    * `Monad.Identity`, `Monad.List` and `Monad.Maybe`:
      The `Identity`, `List`, and `Maybe` monad.
  * **`Parameterized`**:
    Formalizations of different parameterized monads.
    * `Parameterized.IndexedMonad`: 
      Formalization and proofs for indexed monads that model pre- and post-state (Hoare triples).
    * `Parameterized.EffectMonad`:
      Formalization of effect monads that are parameterized by a monoid (*WIP*).
* **`Identity`**:
  Contains some basic stuff about the identity and the identity type function.
  Provides an identity Kleisli-arrow that is polymorphic over the identity type
  constructor; this is central to the formalization of polymonads.
* **`Polymonad`**:
  Formalization of polymonads (slightly altered from the version in Hicks paper).
  The submodules contain proofs and formalizations of other polymonad concepts.
  * `Polymonad.Identity`: 
    The identity polymonad.
  * `Polymonad.Unionable`: 
    The formalization of what is required to 
    union two polymonads that do not have morphisms between them.
  * `Polymonad.Union`: 
    The proof that `UnionablePolymonad`s actually form a polymonad again.
  * `Polymonad.Union.Principal`: 
    Proof that union preserves principality (under some preconditions).
  * `Polymonad.Principal`: 
    The formalization of principal polymonads.
  * `Polymonad.UniqueBinds`: 
    Proof that bind-operations on the same type 
    are unique, i.e., bind-operations with the same type have the same semantics.
* **`Hicks`**:
  Contains a formalization of Hicks polymonads without 
  my alteration. 
  * `Hicks.Equivalency` shows that both formulations are equivalent.
  * `Hicks.UniqueBinds` shows that bind-operations are unique in this formalization of polymonads as well.
* **`MorphMonad`**: 
  These modules contain ideas about the union of standard monads to polymonads by providing lifting
  functions (morphisms) between them (discontinued).
* **`Supermonad`**:
  Another approach to generalizing different kinds of monads, that we call Supermonads. 
  This approach is driven by practical examples of generalized monads.
* **`Theory`**:
  Formalization of category theory to give a category theoretic model of supermonads.
  Contains the proofs that several supermonads are equivalent to lax 2-functors as examples.
