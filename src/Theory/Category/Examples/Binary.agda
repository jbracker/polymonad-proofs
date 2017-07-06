
-- Stdlib
open import Level

open import Data.Unit
open import Data.Empty
open import Data.Bool

open import Relation.Binary.PropositionalEquality

open import Extensionality
open import ProofIrrelevance
open import Theory.Category.Definition

module Theory.Category.Examples.Binary where

-------------------------------------------------------------------------------
-- The Binary Category
-------------------------------------------------------------------------------

binaryCategory : Category {zero} {zero}
binaryCategory = record
  { Obj = Bool
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → comp {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = λ {a} {b} {c} {d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = λ {a} {b} {f} → left-id {a} {b} {f}
  ; right-id = λ {a} {b} {f} → right-id {a} {b} {f}
  } where
    Hom : Bool → Bool → Set zero
    Hom true  true  = ⊤
    Hom false true  = ⊤
    Hom false false = ⊤
    Hom _ _ = ⊥

    comp : {a b c : Bool} → Hom b c → Hom a b → Hom a c
    comp {true}  {true}  {true}  f g = tt
    comp {true}  {true}  {false} () g
    comp {true}  {false} {true}  f g = tt
    comp {true}  {false} {false} f ()
    comp {false} {true}  {true}  f g = tt
    comp {false} {true}  {false} f g = tt
    comp {false} {false} {true}  f g = tt
    comp {false} {false} {false} f g = tt

    id : {a : Bool} → Hom a a
    id {true}  = tt
    id {false} = tt

    abstract
      assoc : {a b c d : Bool} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
            → comp {a} {c} {d} h (comp {a} {b} {c} g f) ≡ comp {a} {b} {d} (comp {b} {c} {d} h g) f
      assoc {true}  {true}  {true}  {true}  {tt} {tt} {tt} = refl
      assoc {true}  {true}  {true}  {false} {tt} {tt} {()}
      assoc {true}  {true}  {false} {d}     {tt} {()} {h}
      assoc {true}  {false} {c}     {d}     {()} {g}  {h}
      assoc {false} {true}  {true}  {true}  {tt} {tt} {tt} = refl
      assoc {false} {true}  {true}  {false} {tt} {tt} {()}
      assoc {false} {true}  {false} {d}     {tt} {()} {h}
      assoc {false} {false} {true}  {true}  {tt} {tt} {tt} = refl
      assoc {false} {false} {true}  {false} {tt} {tt} {()}
      assoc {false} {false} {false} {true}  {tt} {tt} {tt} = refl
      assoc {false} {false} {false} {false} {tt} {tt} {tt} = refl

    abstract
      right-id : {a b : Bool} {f : Hom a b} → comp {a} {b} {b} (id {b}) f ≡ f
      right-id {true} {true} {tt} = refl
      right-id {true} {false} {()}
      right-id {false} {true} {tt} = refl
      right-id {false} {false} {tt} = refl

    abstract
      left-id : {a b : Bool} {f : Hom a b} → comp {a} {a} {b} f (id {a}) ≡ f
      left-id {true} {true} {tt} = refl
      left-id {true} {false} {()}
      left-id {false} {true} {tt} = refl
      left-id {false} {false} {tt} = refl
 
