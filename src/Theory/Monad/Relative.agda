
module Theory.Monad.Relative where

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
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

open Category hiding ( right-id ; left-id )

-- -----------------------------------------------------------------------------
-- Definition of a relative monad
-- -----------------------------------------------------------------------------
record RelativeMonad {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (T : Obj C → Obj D) (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  private
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C
  
  field
    η : {a : Obj C} → Hom D ([ J ]₀ a) (T a)
    kext : {a b : Obj C} → Hom D ([ J ]₀ a) (T b) → Hom D (T a) (T b)
    
    right-id : {a b : Obj C} {k : Hom D ([ J ]₀ a) (T b)} 
             → kext k ∘D η ≡ k
    left-id : {a : Obj C} → kext η ≡ id D {a = T a}
    
    coher : {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T b)} {l : Hom D ([ J ]₀ b) (T c)} 
          → kext ( (kext l) ∘D k ) ≡ kext l ∘D kext k
  
  FunctorT : Functor C D
  FunctorT = functor T (λ f → kext (η ∘D [ J ]₁ f)) fun-id compose
    where
      abstract
        fun-id : {a : Obj C} → kext {a = a} (η ∘D [ J ]₁ (id C)) ≡ id D
        fun-id = trans (trans (cong (λ X → kext (η ∘D X)) (Functor.id J)) (cong kext (Category.left-id D))) left-id
      
      abstract
        compose : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
                → kext (η ∘D [ J ]₁ (g ∘C f)) ≡ kext (η ∘D [ J ]₁ g) ∘D (kext (η ∘D [ J ]₁ f))
        compose {f = f} {g} = trans (cong kext (trans (trans (trans (cong (λ X → η ∘D X) (Functor.compose J)) (assoc D)) (cong (λ X → X ∘D [ J ]₁ f) (sym right-id))) (sym $ assoc D))) coher
  
  functor-kext-coher : {a b : Obj C} → (f : Hom C a b)
                     → [ FunctorT ]₁ f ≡ kext (η ∘D [ J ]₁ f)
  functor-kext-coher f = refl
  
  NaturalTransformation-η : NaturalTransformation J FunctorT
  NaturalTransformation-η = naturalTransformation (λ _ → η) right-id
  
  NaturalTransformation-kext : NaturalTransformation FunctorT FunctorT
  NaturalTransformation-kext = naturalTransformation (λ x → kext (η {x})) natural
    where
      abstract
        natural : {a b : Obj C} {f : Hom C a b} →
                kext (η ∘D [ J ]₁ f) ∘D kext η ≡ kext η ∘D kext (η ∘D [ J ]₁ f)
        natural {f = f} = begin
          kext (η ∘D [ J ]₁ f) ∘D kext η 
            ≡⟨ cong (λ X → kext (η ∘D [ J ]₁ f) ∘D X) left-id ⟩
          kext (η ∘D [ J ]₁ f) ∘D id D
            ≡⟨ Category.left-id D ⟩
          kext (η ∘D [ J ]₁ f)
            ≡⟨ cong kext (sym $ Category.right-id D) ⟩
          kext (id D ∘D (η ∘D [ J ]₁ f))
            ≡⟨ cong (λ X → kext (X ∘D (η ∘D [ J ]₁ f))) (sym left-id) ⟩
          kext (kext η ∘D (η ∘D [ J ]₁ f))
            ≡⟨ coher ⟩
          kext η ∘D kext (η ∘D [ J ]₁ f) ∎


-- -----------------------------------------------------------------------------
-- Relative monads on endofunctors are equivalent to kleisli triples
-- -----------------------------------------------------------------------------
open import Theory.Monad.Kleisli

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
