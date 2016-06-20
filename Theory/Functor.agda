
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
open import Utilities
open import Theory.Category

open Category hiding ( id )

-------------------------------------------------------------------------------
-- Definition of a Functor
-------------------------------------------------------------------------------
record Functor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁}) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor functor
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {a b} → Hom C a b → Hom D (F₀ a) (F₀ b)
    
    id : ∀ {a} → F₁ {a} {a} (Category.id C) ≡ Category.id D
    
    dist : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
         → F₁ (_∘_ C g f) ≡ _∘_ D (F₁ g) (F₁ f)

[_]₀_ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
      → Functor C D → ( Obj C → Obj D )
[_]₀_ F a = Functor.F₀ F a

[_]₁_ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {a b : Obj C} 
      → (F : Functor C D) → ( Hom C a b → Hom D ([ F ]₀ a) ([ F ]₀ b) )
[_]₁_ F f = Functor.F₁ F f

-------------------------------------------------------------------------------
-- The Identity Functor
-------------------------------------------------------------------------------
idFunctor : {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) → Functor C C
idFunctor C = record 
  { F₀ = idF 
  ; F₁ = idF 
  ; id = refl 
  ; dist = refl
  }

Id[_] : {ℓC₀ ℓC₁ : Level} → (C : Category {ℓC₀} {ℓC₁}) → Functor C C
Id[ C ] = idFunctor C

-------------------------------------------------------------------------------
-- Composition of Functors
-------------------------------------------------------------------------------
compFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
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

[_]∘[_] = compFunctor

-------------------------------------------------------------------------------
-- Product of Functors
-------------------------------------------------------------------------------
open Category

productFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ ℓK₀ ℓK₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}} {K : Category {ℓK₀} {ℓK₁}}
               → Functor C D → Functor E K → Functor (C ×C E) (D ×C K)
productFunctor {C = C} {D} {E} {K} F G = record 
  { F₀ = P₀ 
  ; F₁ = P₁ 
  ; id = cong₂ (λ X Y → X , Y) (Functor.id F) (Functor.id G)
  ; dist = cong₂ (λ X Y → X , Y) (Functor.dist F) (Functor.dist G)
  } where
    C×E = C ×C E
    D×K = D ×C K
    
    P₀ : Obj C×E → Obj D×K
    P₀ (ca , ea) = [ F ]₀ ca , [ G ]₀ ea 
    
    P₁ : {a b : Obj C×E} → Hom C×E a b → Hom D×K (P₀ a) (P₀ b)
    P₁ (f , g) = [ F ]₁ f , [ G ]₁ g
    
[_]×[_] = productFunctor

-------------------------------------------------------------------------------
-- Propositional Equality of Functors
-------------------------------------------------------------------------------
propEqFunctor : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
              → {F₀ G₀ : Obj C → Obj D}
              → {F₁ : (a b : Obj C) → Hom C a b → Hom D (F₀ a) (F₀ b)}
              → {G₁ : (a b : Obj C) → Hom C a b → Hom D (G₀ a) (G₀ b)}
              → {idF : {a : Obj C} → F₁ a a (id C) ≡ id D}
              → {idG : {a : Obj C} → G₁ a a (id C) ≡ id D}
              → {distF : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → F₁ a c (_∘_ C g f) ≡ _∘_ D (F₁ b c g) (F₁ a b f)}
              → {distG : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → G₁ a c (_∘_ C g f) ≡ _∘_ D (G₁ b c g) (G₁ a b f)}
              → (eq₀ : F₀ ≡ G₀)
              → (eq₁ : F₁ ≡ subst₂ (λ X Y → (a b : Obj C) → Hom C a b → Hom D (X a) (Y b)) (sym eq₀) (sym eq₀) G₁ )
              → functor {C = C} {D = D} F₀ (λ {a b} → F₁ a b) idF distF ≡ functor {C = C} {D = D} G₀ (λ {a b} → G₁ a b) idG distG
propEqFunctor {F₀ = F₀} {F₁ = F₁} {idF = idF} {idG} {distF} {distG} refl refl = cong₂ (functor F₀ (λ {a b} → F₁ a b)) p1 p2
  where
    p1 = funExtImplicit (λ a → proof-irrelevance (idF {a}) (idG {a}))
    p2 = funExtImplicit 
           (λ a → funExtImplicit 
           (λ b → funExtImplicit
           (λ c → funExtImplicit
           (λ f → funExtImplicit
           (λ g → proof-irrelevance (distF {a} {b} {c} {f} {g}) (distG {a} {b} {c} {f} {g})
           ) ) ) ) )