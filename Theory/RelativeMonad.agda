
module Theory.RelativeMonad where

-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category
open import Theory.Functor

open Category hiding ( idR ; idL )

-- -----------------------------------------------------------------------------
-- Definition of a relative monad
-- -----------------------------------------------------------------------------
record RelativeMonad {ℓ : Level} {C D : Category {ℓ = ℓ}} (T : Obj C → Obj D) (J : Functor C D) : Set ℓ where
  field
    η : {a : Obj C} → Hom D ([ J ]₀ a) (T a)
    kext : {a b : Obj C} → Hom D ([ J ]₀ a) (T b) → Hom D (T a) (T b)
    
    idR : {a b : Obj C} {k : Hom D ([ J ]₀ a) (T b)} 
        → _∘_ D (kext k) η ≡ k
    idL : {a : Obj C} → kext η ≡ id D {a = T a}
    
    coher : {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T b)} {l : Hom D ([ J ]₀ b) (T c)} 
          → kext ( _∘_ D (kext l) k ) ≡ _∘_ D (kext l) (kext k)


-- -----------------------------------------------------------------------------
-- Relative monads on endofunctors are equivalent to kleisli triples
-- -----------------------------------------------------------------------------
open import Theory.Kleisli

RelativeMonad→KleisliTriple : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C} → RelativeMonad T Id[ C ] → KleisliTriple {C = C} T
RelativeMonad→KleisliTriple {C = C} {T = T} rm = record 
  { η = RelativeMonad.η rm 
  ; kext = RelativeMonad.kext rm 
  ; idR = RelativeMonad.idR rm 
  ; idL = RelativeMonad.idL rm 
  ; coher = RelativeMonad.coher rm 
  }

KleisliTriple→RelativeMonad : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C} → KleisliTriple {C = C} T → RelativeMonad T Id[ C ]
KleisliTriple→RelativeMonad kleisli = record 
  { η = KleisliTriple.η kleisli
  ; kext = KleisliTriple.kext kleisli
  ; idR = KleisliTriple.idR kleisli
  ; idL = KleisliTriple.idL kleisli
  ; coher = KleisliTriple.coher kleisli
  }
