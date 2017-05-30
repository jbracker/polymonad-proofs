
open import Level
open import Function hiding ( id )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Theory.Category.Definition
open import Theory.Category.Closed
open import Theory.Category.Isomorphism
open import Theory.Category.Examples renaming ( setCategory to SetCat )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Closed.Examples where

setClosedCategory : {ℓ : Level} → ClosedCategory (SetCat {ℓ})
setClosedCategory {ℓ} = record
  { InternalHom = functor Hom₀ Hom₁ refl refl
  ; I = Lift ⊤
  ; i-natural-isomorphism = naturalIsomorphism 
                          (naturalTransformation (λ α x _ → x) refl) 
                          (λ α → isomorphism (λ f → f (lift tt)) refl refl)
  ; j = λ α x y → y
  ; L = λ α β γ f g → f ∘ g
  ; γ-inv = λ f → f (lift tt)
  ; j-extranatural-a = λ {a} {a'} f → refl
  ; L-natural-c = λ a b {c} {c'} {f} → refl
  ; L-natural-b = λ a c {b} {b'} {f} → refl
  ; L-extranatural-a = λ b c {a} {a'} f → refl
  ; coher-1 = λ x y → refl
  ; coher-2 = λ x y → refl
  ; coher-3 = λ y z → refl
  ; coher-4 = λ x y u v → refl
  ; γ-right-id = λ f → refl
  ; γ-left-id  = λ {x} {y} f → refl
  } where
    C = SetCat {ℓ}
    open Category hiding ( _∘_ )
    open Functor hiding ( id )
    
    Hom₀ : Obj ((C op) ×C C) → Obj C
    Hom₀ (a , b) = a → b
    
    Hom₁ : {a b : Obj ((C op) ×C C)} → Hom ((C op) ×C C) a b → Hom C (Hom₀ a) (Hom₀ b)
    Hom₁ {a , a'} {b , b'} (f , g) h = g ∘ h ∘ f
    
    
