
module Theory.Functor where

-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Data.Unit
open import Relation.Binary.HeterogeneousEquality hiding ( trans ; sym ; cong ; cong₂ ; subst ; proof-irrelevance ) renaming ( refl to hrefl )
open import Relation.Binary.PropositionalEquality

-- Local
open import Utilities
open import Extensionality
open import Theory.Category

open Category hiding ( id )

-------------------------------------------------------------------------------
-- Definition of a Functor
-------------------------------------------------------------------------------
record Functor {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁}) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁) where
  constructor functor
  
  open Category hiding ( id )
  
  private
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
  
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {a b} → Hom C a b → Hom D (F₀ a) (F₀ b)
    
    id : ∀ {a} → F₁ {a} {a} (Category.id C) ≡ Category.id D
    
    compose : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
            → F₁ (g ∘C f) ≡ (F₁ g) ∘D (F₁ f)

[_]₀ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
      → Functor C D → ( Obj C → Obj D )
[_]₀ F a = Functor.F₀ F a

[_]₁ : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {a b : Obj C} 
      → (F : Functor C D) → ( Hom C a b → Hom D ([ F ]₀ a) ([ F ]₀ b) )
[_]₁ F f = Functor.F₁ F f

-------------------------------------------------------------------------------
-- Definition of a Contravariant Functor
-------------------------------------------------------------------------------

-- Contravariant functors offer "F₁ : Hom C b a → Hom D (F₀ a) (F₀ b)"
-- instead of "Hom C a b → Hom D (F₀ a) (F₀ b)"
ContravariantFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁}) → Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁)
ContravariantFunctor C D = Functor (C op) D

-------------------------------------------------------------------------------
-- Definition of Injective Functor 
-------------------------------------------------------------------------------

-- The given functor is considered to be injective iff its object and 
-- homomorphism mapping are injective respectivly.
IsInjectiveFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} 
                   → {D : Category {ℓD₀} {ℓD₁}} 
                   → Functor C D → Set (ℓD₁ ⊔ ℓD₀ ⊔ ℓC₁ ⊔ ℓC₀)
IsInjectiveFunctor {C = C} {D} F = IsInjective (Functor.F₀ F) × ((x y : Category.Obj C) → IsInjective (Functor.F₁ F {x} {y}))

-------------------------------------------------------------------------------
-- The Identity Functor
-------------------------------------------------------------------------------
idFunctor : {ℓ₀ ℓ₁ : Level} (C : Category {ℓ₀} {ℓ₁}) → Functor C C
idFunctor C = record 
  { F₀ = idF 
  ; F₁ = idF 
  ; id = refl 
  ; compose = refl
  }

Id[_] : {ℓC₀ ℓC₁ : Level} → (C : Category {ℓC₀} {ℓC₁}) → Functor C C
Id[ C ] = idFunctor C

-------------------------------------------------------------------------------
-- Composition of Functors
-------------------------------------------------------------------------------
compFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
            → Functor D E → Functor C D → Functor C E
compFunctor {C = C} {D = D} {E = E} F G = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = id
  ; compose = compose
  } where
    F₀ : Obj C → Obj E
    F₀ a = [ F ]₀ ( [ G ]₀ a )
    
    F₁ : {a b : Obj C} → Hom C a b → Hom E (F₀ a) (F₀ b)
    F₁ f = [ F ]₁ ( [ G ]₁ f )
    
    id : ∀ {a : Obj C} → F₁ {a = a} (Category.id C) ≡ Category.id E
    id = trans (cong (λ X → Functor.F₁ F X) (Functor.id G)) (Functor.id F)
    
    compose : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} 
         → F₁ (_∘_ C g f) ≡ _∘_ E (F₁ g) (F₁ f)
    compose = trans (cong (λ X → Functor.F₁ F X) (Functor.compose G)) (Functor.compose F)

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
  ; compose = cong₂ (λ X Y → X , Y) (Functor.compose F) (Functor.compose G)
  } where
    C×E = C ×C E
    D×K = D ×C K
    
    P₀ : Obj C×E → Obj D×K
    P₀ (ca , ea) = [ F ]₀ ca , [ G ]₀ ea 
    
    P₁ : {a b : Obj C×E} → Hom C×E a b → Hom D×K (P₀ a) (P₀ b)
    P₁ (f , g) = [ F ]₁ f , [ G ]₁ g
    
[_]×[_] = productFunctor

-------------------------------------------------------------------------------
-- Constant Functor
-------------------------------------------------------------------------------
constFunctor : {ℓC₀ ℓC₁ : Level} → (C : Category {ℓC₀} {ℓC₁}) → (c : Obj C) → Functor ⊤-Cat C
constFunctor C c = record
  { F₀ = F₀
  ; F₁ = F₁
  ; id = refl
  ; compose = sym (Category.left-id C)
  } where
    F₀ : Obj ⊤-Cat → Obj C
    F₀ tt = c
    
    F₁ : {a b : Obj ⊤-Cat} → Hom ⊤-Cat a b → Hom C (F₀ a) (F₀ b)
    F₁ {a = tt} {b = tt} tt = Category.id C {c}
    
-------------------------------------------------------------------------------
-- Left and right extensions of a Functors result
-------------------------------------------------------------------------------
leftExtendFunctor 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
  → (E : Category {ℓE₀} {ℓE₁}) → Obj E → Functor C D → Functor C (E ×C D)
leftExtendFunctor E e F = record
  { F₀ = λ c → e , [ F ]₀ c
  ; F₁ = λ f → id E {e} , [ F ]₁ f
  ; id = cong₂ _,_ refl (Functor.id F)
  ; compose = cong₂ _,_ (sym (Category.left-id E)) (Functor.compose F)
  }

-- ▷ = \rhd
[_,_]▷[_] = leftExtendFunctor

rightExtendFunctor 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
  → Functor C D → (E : Category {ℓE₀} {ℓE₁}) → Obj E → Functor C (D ×C E)
rightExtendFunctor F E e = record
  { F₀ = λ c → [ F ]₀ c , e
  ; F₁ = λ f → [ F ]₁ f , id E {e}
  ; id = cong₂ _,_ (Functor.id F) refl
  ; compose = cong₂ _,_ (Functor.compose F) (sym (Category.left-id E))
  }

-- ◁ = \lhd
[_]◁[_,_] = rightExtendFunctor

-------------------------------------------------------------------------------
-- Equality of Functors
-------------------------------------------------------------------------------
functor-eq : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
           → {F₀ G₀ : Obj C → Obj D}
           → {F₁ : (a b : Obj C) → Hom C a b → Hom D (F₀ a) (F₀ b)}
           → {G₁ : (a b : Obj C) → Hom C a b → Hom D (G₀ a) (G₀ b)}
           → {idF : {a : Obj C} → F₁ a a (id C) ≡ id D}
           → {idG : {a : Obj C} → G₁ a a (id C) ≡ id D}
           → {composeF : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → F₁ a c (_∘_ C g f) ≡ _∘_ D (F₁ b c g) (F₁ a b f)}
           → {composeG : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → G₁ a c (_∘_ C g f) ≡ _∘_ D (G₁ b c g) (G₁ a b f)}
           → (eq₀ : F₀ ≡ G₀)
           → (eq₁ : F₁ ≅ G₁ )
           → functor {C = C} {D = D} F₀ (λ {a b} → F₁ a b) idF composeF ≡ functor {C = C} {D = D} G₀ (λ {a b} → G₁ a b) idG composeG
functor-eq {F₀ = F₀} {F₁ = F₁} {idF = idF} {idG} {composeF} {composeG} refl hrefl = cong₂ (functor F₀ (λ {a b} → F₁ a b)) p1 p2
  where
    p1 = implicit-fun-ext (λ a → proof-irrelevance (idF {a}) (idG {a}))
    p2 = implicit-fun-ext 
           (λ a → implicit-fun-ext 
           (λ b → implicit-fun-ext
           (λ c → implicit-fun-ext
           (λ f → implicit-fun-ext
           (λ g → proof-irrelevance (composeF {a} {b} {c} {f} {g}) (composeG {a} {b} {c} {f} {g})
           ) ) ) ) )
