
module Theory.Functor where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Theory.Category

open Category hiding ( id )

record Functor {ℓ : Level} (C : Category) (D : Category) : Set ℓ where
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {a b} → Hom C a b → Hom D (F₀ a) (F₀ b)
    
    id : ∀ {a} → F₁ {a} {a} (Category.id C) ≡ Category.id D
    
    dist : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
         → F₁ (_∘_ C g f) ≡ _∘_ D (F₁ g) (F₁ f)

[_]₀_ : ∀ {ℓ} {C D : Category {ℓ = ℓ}} → Functor C D → Obj C → Obj D
[_]₀_ F a = Functor.F₀ F a

[_]₁_ : ∀ {ℓ} {C D : Category {ℓ = ℓ}} {a b : Obj C} 
      → (F : Functor C D) → Hom C a b → Hom D ([ F ]₀ a) ([ F ]₀ b)
[_]₁_ F f = Functor.F₁ F f

idFunctor : ∀ {ℓ} → (C : Category {ℓ = ℓ}) → Functor C C
idFunctor C = record 
  { F₀ = idF 
  ; F₁ = idF 
  ; id = refl 
  ; dist = refl
  }

Id[_] : ∀ {ℓ} → (C : Category {ℓ = ℓ}) → Functor C C
Id[ C ] = idFunctor C

compFunctor : ∀ {ℓ} {C D E : Category {ℓ = ℓ}} 
            → Functor C D → Functor D E → Functor C E
compFunctor {C = C} {D = D} {E = E} F G = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = id
  ; dist = dist
  } where
    F₀ : Obj C → Obj E
    F₀ a = [ G ]₀ ( [ F ]₀ a )
    
    F₁ : {a b : Obj C} → Hom C a b → Hom E (F₀ a) (F₀ b)
    F₁ f = [ G ]₁ ( [ F ]₁ f )
    
    id : ∀ {a : Obj C} → F₁ {a = a} (Category.id C) ≡ Category.id E
    id = trans (cong (λ X → Functor.F₁ G X) (Functor.id F)) (Functor.id G)
    
    dist : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
         → F₁ (_∘_ C g f) ≡ _∘_ E (F₁ g) (F₁ f)
    dist = trans (cong (λ X → Functor.F₁ G X) (Functor.dist F)) (Functor.dist G)

[_]∘[_] : ∀ {ℓ} {C D E : Category {ℓ = ℓ}} 
        → Functor D E → Functor C D → Functor C E
[ G ]∘[ F ] = compFunctor F G
