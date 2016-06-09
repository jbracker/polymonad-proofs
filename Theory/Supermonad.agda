
module Theory.Supermonad where

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
-- Definition of a categorical supermonad
-- -----------------------------------------------------------------------------
record Supermonad {ℓ : Level} {C D E : Category {ℓ = ℓ}} (T : {a b : Obj E} → Hom E a b → Obj C → Obj D) (J : Functor C D) : Set ℓ where
  field
    η : {a : Obj C} {e : Obj E} → Hom D ([ J ]₀ a) (T (id E {a = e}) a)
    kext : {a b : Obj C} {e₁ e₂ e₃ : Obj E} {f : Hom E e₂ e₃} {g : Hom E e₁ e₂} → Hom D ([ J ]₀ a) (T f b) → Hom D (T g a) (T (_∘_ E f g) b)
    
    idR : {a b : Obj C} {e₁ e₂ : Obj E} {f : Hom E e₁ e₂} {k : Hom D ([ J ]₀ a) (T f b)} 
        → _∘_ D (kext k) η ≡ subst (λ X → Hom D ([ J ]₀ a) (T X b)) (sym (Category.idR E)) k
    idL : {a : Obj C} {e₁ e₂ : Obj E} {f : Hom E e₁ e₂} 
        → kext {g = f} η ≡ subst (λ X → Hom D (T f a) (T X a)) (sym (Category.idL E)) (id D {a = T f a})
    
    coher : {a b c : Obj C} 
          → {e₀ e₁ e₂ e₃ : Obj E} {f : Hom E e₁ e₂} {g : Hom E e₀ e₁} {h : Hom E e₂ e₃}
          → {k : Hom D ([ J ]₀ a) (T f b)} {l : Hom D ([ J ]₀ b) (T h c)} 
          → kext ( _∘_ D (kext l) k ) ≡ subst (λ X → Hom D (T g a) (T X c)) (assoc E) ( _∘_ D (kext l) (kext k) )

-- -----------------------------------------------------------------------------
-- Supermonads are a generalization of relative monads
-- -----------------------------------------------------------------------------
open import Theory.RelativeMonad

Supermonad→RelativeMonad : {ℓ : Level} {C D : Category {ℓ = ℓ}} {T : Obj C → Obj D} {J : Functor C D} 
                         → Supermonad {E = UnitCategory} (const {b = ℓ} T) J → RelativeMonad T J
Supermonad→RelativeMonad sm = record 
  { η = Supermonad.η sm
  ; kext = Supermonad.kext sm
  ; idR = Supermonad.idR sm
  ; idL = Supermonad.idL sm
  ; coher = Supermonad.coher sm
  }

RelativeMonad→Supermonad : {ℓ : Level} {C D : Category {ℓ = ℓ}} {T : Obj C → Obj D} {J : Functor C D} 
                         → RelativeMonad T J → Supermonad {E = UnitCategory} (const {b = ℓ} T) J
RelativeMonad→Supermonad rm = record 
  { η = RelativeMonad.η rm 
  ; kext = RelativeMonad.kext rm 
  ; idR = RelativeMonad.idR rm 
  ; idL = RelativeMonad.idL rm 
  ; coher = RelativeMonad.coher rm
  }

-- -----------------------------------------------------------------------------
-- Supermonads are a generalization of kleisli triples
-- -----------------------------------------------------------------------------
open import Theory.Kleisli

Supermonad→KleisliTriple : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C} 
                         → Supermonad {E = UnitCategory} (const {b = ℓ} T) Id[ C ] → KleisliTriple {C = C} T
Supermonad→KleisliTriple sm = RelativeMonad→KleisliTriple (Supermonad→RelativeMonad sm)

KleisliTriple→Supermonad : {ℓ : Level} {C : Category {ℓ = ℓ}} {T : Obj C → Obj C} 
                         → KleisliTriple {C = C} T → Supermonad {E = UnitCategory} (const {b = ℓ} T) Id[ C ] 
KleisliTriple→Supermonad kleisli = RelativeMonad→Supermonad (KleisliTriple→RelativeMonad kleisli)
