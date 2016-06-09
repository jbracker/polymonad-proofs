
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
record Supermonad {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} 
                  (T : {a b : Obj E} → Hom E a b → Functor C D) (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓE₀ ⊔ ℓE₁) where
  field
    η : {a : Obj C} {e : Obj E} → Hom D ([ J ]₀ a) ([ T (id E {a = e}) ]₀ a)
    kext : {a b : Obj C} {e₁ e₂ e₃ : Obj E} {f : Hom E e₂ e₃} {g : Hom E e₁ e₂} → Hom D ([ J ]₀ a) ([ T f ]₀ b) → Hom D ([ T g ]₀ a) ([ T (_∘_ E f g) ]₀ b)
    
    idR : {a b : Obj C} {e₁ e₂ : Obj E} {f : Hom E e₁ e₂} {k : Hom D ([ J ]₀ a) ([ T f ]₀ b)} 
        → _∘_ D (kext k) η ≡ subst (λ X → Hom D ([ J ]₀ a) ([ T X ]₀ b)) (sym (Category.idR E)) k
    idL : {a : Obj C} {e₁ e₂ : Obj E} {f : Hom E e₁ e₂} 
        → kext {g = f} η ≡ subst (λ X → Hom D ([ T f ]₀ a) ([ T X ]₀ a)) (sym (Category.idL E)) (id D {a = [ T f ]₀ a})
    
    coher : {a b c : Obj C} 
          → {e₀ e₁ e₂ e₃ : Obj E} {f : Hom E e₁ e₂} {g : Hom E e₀ e₁} {h : Hom E e₂ e₃}
          → {k : Hom D ([ J ]₀ a) ([ T f ]₀ b)} {l : Hom D ([ J ]₀ b) ([ T h ]₀ c)} 
          → kext ( _∘_ D (kext l) k ) ≡ subst (λ X → Hom D ([ T g ]₀ a) ([ T X ]₀ c)) (assoc E) ( _∘_ D (kext l) (kext k) )
{-
-- -----------------------------------------------------------------------------
-- For all indices 'e' 'T e' forms a functor 
-- -----------------------------------------------------------------------------
Supermonad→FunctorT : {ℓ : Level} {C D E : Category {ℓ = ℓ}}
                    → {T : {a b : Obj E} → Hom E a b → Obj C → Obj D} {J : Functor C D} 
                    → {a b : Obj E} → Hom E a b → Supermonad {C = C} {D = D} {E = E} T J → Functor C D
Supermonad→FunctorT {C = C} {D = D} {E = E} {T = T} {J = J} e sm = record 
  { F₀ = F₀ 
  ; F₁ = {!!} 
  ; id = {!!} 
  ; dist = {!!} 
  } where
    η = Supermonad.η sm
    kext = Supermonad.kext sm
    _∘C_ = Category._∘_ C
    _∘D_ = Category._∘_ D
    
    F₀ : Obj C → Obj D
    F₀ = T e
    
    F₁ : {a b : Obj C} → Hom C a b → Hom D (F₀ a) (F₀ b)
    F₁ f = {!kext (η ∘C f)!} -- This does not work because we don't know how to convert Hom C to Hom D just from T and the laws.
-}
-- -----------------------------------------------------------------------------
-- Supermonads are a generalization of relative monads
-- -----------------------------------------------------------------------------
open import Theory.RelativeMonad

Supermonad→RelativeMonad : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {T : Functor C D} {J : Functor C D} 
                         → Supermonad {E = unitCategory {ℓE₀} {ℓE₁}} (const T) J → RelativeMonad (Functor.F₀ T) J
Supermonad→RelativeMonad sm = record 
  { η = Supermonad.η sm
  ; kext = Supermonad.kext sm
  ; idR = Supermonad.idR sm
  ; idL = Supermonad.idL sm
  ; coher = Supermonad.coher sm
  }

RelativeMonad→Supermonad : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {T : Functor C D} {J : Functor C D} 
                         → RelativeMonad (Functor.F₀ T) J → Supermonad {E = unitCategory {ℓE₀} {ℓE₁}} (const T) J
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

Supermonad→KleisliTriple : {ℓC₀ ℓC₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Functor C C} 
                         → Supermonad {E = unitCategory {ℓE₀} {ℓE₁}} (const T) Id[ C ] → KleisliTriple {C = C} (Functor.F₀ T)
Supermonad→KleisliTriple sm = RelativeMonad→KleisliTriple (Supermonad→RelativeMonad sm)

KleisliTriple→Supermonad : {ℓC₀ ℓC₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {T : Functor C C} 
                         → KleisliTriple {C = C} (Functor.F₀ T) → Supermonad {E = unitCategory {ℓE₀} {ℓE₁}} (const T) Id[ C ] 
KleisliTriple→Supermonad kleisli = RelativeMonad→Supermonad (KleisliTriple→RelativeMonad kleisli)
