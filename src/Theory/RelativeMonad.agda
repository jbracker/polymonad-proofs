
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

open Category hiding ( right-id ; left-id )

-- -----------------------------------------------------------------------------
-- Definition of a relative monad
-- -----------------------------------------------------------------------------
record RelativeMonad {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (T : Obj C → Obj D) (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  private
    _∘D_ = _∘_ D
  
  field
    η : {a : Obj C} → Hom D ([ J ]₀ a) (T a)
    kext : {a b : Obj C} → Hom D ([ J ]₀ a) (T b) → Hom D (T a) (T b)
    
    right-id : {a b : Obj C} {k : Hom D ([ J ]₀ a) (T b)} 
             → _∘_ D (kext k) η ≡ k
    left-id : {a : Obj C} → kext η ≡ id D {a = T a}
    
    coher : {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T b)} {l : Hom D ([ J ]₀ b) (T c)} 
          → kext ( kext l ∘D k ) ≡ kext l ∘D kext k


-- -----------------------------------------------------------------------------
-- Relative monads on endofunctors are equivalent to kleisli triples
-- -----------------------------------------------------------------------------
open import Theory.Kleisli

RelativeMonad→KleisliTriple : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Obj C → Obj C} 
                            → RelativeMonad T Id[ C ] → KleisliTriple {C = C} T
RelativeMonad→KleisliTriple {C = C} {T = T} rm = record 
  { η = RelativeMonad.η rm 
  ; kext = RelativeMonad.kext rm 
  ; right-id = RelativeMonad.right-id rm 
  ; left-id = RelativeMonad.left-id rm 
  ; coher = RelativeMonad.coher rm 
  }

KleisliTriple→RelativeMonad : {ℓC₀ ℓC₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Obj C → Obj C} 
                            → KleisliTriple {C = C} T → RelativeMonad T Id[ C ]
KleisliTriple→RelativeMonad kleisli = record 
  { η = KleisliTriple.η kleisli
  ; kext = KleisliTriple.kext kleisli
  ; right-id = KleisliTriple.right-id kleisli
  ; left-id = KleisliTriple.left-id kleisli
  ; coher = KleisliTriple.coher kleisli
  }
