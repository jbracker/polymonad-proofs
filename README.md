 
# Polymonad Formalization and Proofs

This repository contains a formalization of polymonads in Agda as 
presented in the paper 
["Polymonadic Programming" by Hicks et al. (MSFP 2014)](http://www.cs.bham.ac.uk/~pbl/msfp2014/polymonad.pdf).

The formalization is targeted to provide proofs that are useful for
the Haskell implementation of polymonads. Therefore, some of the
formalizations assume we are working in a "Haskell World".

## Type Checking and Versions

Calling `make` should type check all files that don't contain 
unsolved holes.

This was tested with Agda in version `2.4.2.5` and the Adga standard library 
in version `0.11`. If you have problems type checking the code, please contact
me.

## Module Structure and Guide

* **`Haskell` and `Utilities`**:
  Basic stuff to formalize things related to Haskell and provide utilities that
  are used throughout. Function extensionality is formalized in the `Utilities`
  module.
* **`Identity`**:
  Contains some basic stuff about the identity and the identity type function.
  Provides an identity Kleisli-arrow that is polymorphic over the identity type
  constructor; this is central to the formalization of polymonads.
* **`Monad`**:
  Formalization of monads as they are represented in Haskell.
  * `Monad.Polymonad`, `Monad.Unionable` and `Monad.Principal`:
    Monads form polymonads, are unionable, and principal.
  * `Monad.PrincipalUnion`:
    A specialised proof that the union of monads forms a principal polymonad.
  * `Monad.Identity`, `Monad.List` and `Monad.Maybe`:
    The `Identity`, `List`, and `Maybe` monad.
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
* **`Parameterized`**:
  Formalizations of different parameterized monads.
  * `Parameterized.IndexedMonad`: 
    Formalization and proofs for indexed monads that model pre- and post-state (Hoare triples).
  * `Parameterized.EffectMonad`:
    Formalization of effect monads that are parameterized by a monoid (*WIP*).
* **`Hicks`**:
  Contains a formalization of Hicks polymonads without 
  my alteration. 
  * `Hicks.Equivalency` shows that both formulations are equivalent.
  * `Hicks.UniqueBinds` shows that bind-operations are unique in this formalization of polymonads as well.
* **`MorphMonad`**: 
  These modules contain ideas about the union of standard monads to polymonads by providing lifting
  functions (morphisms) between them (*WIP*).