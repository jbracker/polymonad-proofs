
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Data.Unit
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong ; cong₂ to hcong₂ ; proof-irrelevance to hproof-irrelevance )
open import Relation.Binary.PropositionalEquality

-- Local
open import Utilities
open import Extensionality
open import Theory.Category.Definition

module Theory.Functor.Definition where

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
-- Definition of different functor properties
-------------------------------------------------------------------------------

private
  module Properties {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (F : Functor C D) where
    open Category
    open Functor
    
    IsFaithfulFunctor : Set (ℓD₁ ⊔ ℓC₁ ⊔ ℓC₀)
    IsFaithfulFunctor = (a b : Obj C) → IsInjective (F₁ F {a} {b})

    IsFullFunctor : Set (ℓD₁ ⊔ ℓC₁ ⊔ ℓC₀)
    IsFullFunctor = (a b : Obj C) → IsSurjective (F₁ F {a} {b})

    IsFullyFaithfulFunctor : Set (ℓD₁ ⊔ (ℓC₁ ⊔ ℓC₀))
    IsFullyFaithfulFunctor = (a b : Obj C) → IsBijective (F₁ F {a} {b})
    
open Properties public

-------------------------------------------------------------------------------
-- Definition of Injective Functor 
-------------------------------------------------------------------------------

-- The given functor is considered to be injective iff its object and 
-- homomorphism mapping are injective respectivly.
IsInjectiveFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} 
                   → {D : Category {ℓD₀} {ℓD₁}} 
                   → Functor C D → Set (ℓD₁ ⊔ ℓD₀ ⊔ ℓC₁ ⊔ ℓC₀)
IsInjectiveFunctor {C = C} {D} F = IsInjective (Functor.F₀ F) × IsFaithfulFunctor F

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
-- The opposite Functor
-------------------------------------------------------------------------------
oppositeFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                → Functor C D → Functor (C op) (D op)
oppositeFunctor (functor F₀ F₁ id compose) = functor F₀ F₁ id compose

oppositeFunctor' : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                 → Functor (C op) (D op) → Functor C D
oppositeFunctor' (functor F₀ F₁ id compose) = functor F₀ F₁ id compose

[_]op  = oppositeFunctor
[_]op' = oppositeFunctor'

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
constObjFunctor : {ℓC₀ ℓC₁ : Level} 
                → (C : Category {ℓC₀} {ℓC₁}) → (c : Obj C) 
                → Functor ⊤-Cat C
constObjFunctor C c = record
  { F₀ = F₀
  ; F₁ = F₁
  ; id = refl
  ; compose = sym (Category.left-id C)
  } where
    F₀ : Obj ⊤-Cat → Obj C
    F₀ tt = c
    
    F₁ : {a b : Obj ⊤-Cat} → Hom ⊤-Cat a b → Hom C (F₀ a) (F₀ b)
    F₁ {a = tt} {b = tt} tt = Category.id C {c}

constToAnyFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} (C : Category {ℓC₀} {ℓC₁}) {D : Category {ℓD₀} {ℓD₁}}
                  → Functor ⊤-Cat D → Functor C D
constToAnyFunctor C (functor F₀ F₁ id compose) = functor (λ _ → F₀ tt) (λ _ → F₁ tt) id compose

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
abstract
  functor-eq : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
             → {F₀ G₀ : Obj C → Obj D}
             → {F₁ : {a b : Obj C} → Hom C a b → Hom D (F₀ a) (F₀ b)}
             → {G₁ : {a b : Obj C} → Hom C a b → Hom D (G₀ a) (G₀ b)}
             → {idF : {a : Obj C} → F₁ {a} {a} (id C) ≡ id D}
             → {idG : {a : Obj C} → G₁ {a} {a} (id C) ≡ id D}
             → {composeF : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → F₁ {a} {c} (_∘_ C g f) ≡ _∘_ D (F₁ {b} {c} g) (F₁ {a} {b} f)}
             → {composeG : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → G₁ {a} {c} (_∘_ C g f) ≡ _∘_ D (G₁ {b} {c} g) (G₁ {a} {b} f)}
             → (eq₀ : F₀ ≡ G₀)
             → (eq₁ : (λ {a} {b} → F₁ {a} {b}) ≅ (λ {a} {b} → G₁ {a} {b}) )
             → functor {C = C} {D = D} F₀ (λ {a} {b} → F₁ {a} {b}) idF composeF ≡ functor {C = C} {D = D} G₀ (λ {a} {b} → G₁ {a} {b}) idG composeG
  functor-eq {F₀ = F₀} {F₁ = F₁} {idF = idF} {idG} {composeF} {composeG} refl hrefl = cong₂ (functor F₀ (λ {a} {b} → F₁ {a} {b})) p1 p2
    where
      p1 = implicit-fun-ext (λ a → proof-irrelevance (idF {a}) (idG {a}))
      p2 = implicit-fun-ext 
             (λ a → implicit-fun-ext 
             (λ b → implicit-fun-ext
             (λ c → implicit-fun-ext
             (λ f → implicit-fun-ext
             (λ g → proof-irrelevance (composeF {a} {b} {c} {f} {g}) (composeG {a} {b} {c} {f} {g})
             ) ) ) ) )

abstract
  het-functor-eq : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} {C : Category {Cℓ₀} {Cℓ₁}} {D : Category {Dℓ₀} {Dℓ₁}} 
                 → {F₀ G₀ : Obj C → Obj D}
                 → {F₁ : (a b : Obj C) → Hom C a b → Hom D (F₀ a) (F₀ b)}
                 → {G₁ : (a b : Obj C) → Hom C a b → Hom D (G₀ a) (G₀ b)}
                 → {idF : {a : Obj C} → F₁ a a (id C) ≡ id D}
                 → {idG : {a : Obj C} → G₁ a a (id C) ≡ id D}
                 → {composeF : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → F₁ a c (_∘_ C g f) ≡ _∘_ D (F₁ b c g) (F₁ a b f)}
                 → {composeG : ∀ {a b c} {f : Hom C a b} {g : Hom C b c} → G₁ a c (_∘_ C g f) ≡ _∘_ D (G₁ b c g) (G₁ a b f)}
                 → (eq₀ : F₀ ≅ G₀)
                 → (eq₁ : F₁ ≅ G₁ )
                 → functor {C = C} {D = D} F₀ (λ {a b} → F₁ a b) idF composeF ≅ functor {C = C} {D = D} G₀ (λ {a b} → G₁ a b) idG composeG
  het-functor-eq {F₀ = F₀} {F₁ = F₁} {idF = idF} {idG} {composeF} {composeG} hrefl hrefl = hcong₂ (functor F₀ (λ {a b} → F₁ a b)) p1 p2
    where
      p1 = het-implicit-fun-ext hrefl (λ a → ≡-to-≅ $ proof-irrelevance (idF {a}) (idG {a}))
      p2 = het-implicit-fun-ext hrefl
             (λ a → het-implicit-fun-ext hrefl
             (λ b → het-implicit-fun-ext hrefl
             (λ c → het-implicit-fun-ext hrefl
             (λ f → het-implicit-fun-ext hrefl
             (λ g → ≡-to-≅ $ proof-irrelevance (composeF {a} {b} {c} {f} {g}) (composeG {a} {b} {c} {f} {g})
             ) ) ) ) )
