 
# Polymonad Formalization and Proofs

This repository contains a formalization of polymonads in Agda as 
presented in the paper 
["Polymonadic Programming" by Hicks et al. (MSFP 2014)](http://www.cs.bham.ac.uk/~pbl/msfp2014/polymonad.pdf).

## Module Structure

* **`Haskell` and `Utilities`**:
  Basic stuff to formalize things related to Haskell and provide utilities that
  are used throughout. Function extensionality is formalized in the `Utilities`
  module.
* **`Identity`**:
  Contains some basic stuff about the identity and the identity type function.
  Provides a identity Kleisli-arrow that is polymorphic over the identity type
  constructor; this is central to the formalization of polymonads.