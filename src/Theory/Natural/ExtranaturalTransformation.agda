
open import Level
open import Function hiding ( _∘_ ; id )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Application
open import Theory.Natural.Transformation

open TriFunctor

module Theory.Natural.ExtranaturalTransformation where

-------------------------------------------------------------------------------
-- Definition of extranatural transformations
-------------------------------------------------------------------------------
record ExtranaturalTransformation {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                                  {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
                                  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                  (F : Functor (A ×C B op ×C B) D)
                                  (G : Functor (A ×C C op ×C C) D)
                                  : Set (ℓA₀ ⊔  ℓA₁ ⊔ ℓC₀ ⊔ ℓC₁ ⊔ ℓB₀ ⊔ ℓB₁ ⊔ ℓD₁) where
  constructor extranatural-transformation
  open Category
  private
    _∘D_ = _∘_ D
  field
    η : (a : Obj A) → (b : Obj B) → (c : Obj C)
      → Hom D ([ F ]₀ (a , b , b)) ([ G ]₀ (a , c , c))
    
    η-natural : (b : Obj B) → (c : Obj C)
              → {x y : Obj A} {f : Hom A x y}
              → ([ ([-, c , c ] G) ]₁ f) ∘D η x b c ≡ η y b c ∘D ([ ([-, b , b ] F) ]₁ f)
            -- G₁ f ∘ η ≡ η ∘ F₁ f
  
  η-natural-transformation : (b : Obj B) → (c : Obj C)
                           → NaturalTransformation ([-, b , b ] F) ([-, c , c ] G)
  η-natural-transformation b c = naturalTransformation (λ a → η a b c) (η-natural b c)

  field
    extranatural : (a : Obj A) → (b : Obj B) → {c c' : Obj C} → (f : Hom C c c')
                 → [ G ]₁ (id A , f         , id C) ∘D η a b c'
                 ≡ [ G ]₁ (id A , id (C op) , f   ) ∘D η a b c
    
    extranatural-op : (a : Obj A) → (c : Obj C) → {b b' : Obj B} → (f : Hom B b b')
                    → η a b' c ∘D [ F ]₁ (id A , id (B op) , f   )
                    ≡ η a b  c ∘D [ F ]₁ (id A , f         , id B)

open Category

extranatural-transformation-eq 
  : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
  → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}}
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
  → {F : Functor (A ×C B op ×C B) D}
  → {G : Functor (A ×C C op ×C C) D}
  → {η₀ : (a : Obj A) → (b : Obj B) → (c : Obj C) → Hom D ([ F ]₀ (a , b , b)) ([ G ]₀ (a , c , c))}
  → {η₁ : (a : Obj A) → (b : Obj B) → (c : Obj C) → Hom D ([ F ]₀ (a , b , b)) ([ G ]₀ (a , c , c))}
  → {nat₀ : (b : Obj B) → (c : Obj C) → {x y : Obj A} {f : Hom A x y} → _∘_ D ([ ([-, c , c ] G) ]₁ f) (η₀ x b c) ≡ _∘_ D (η₀ y b c) ([ ([-, b , b ] F) ]₁ f)}
  → {nat₁ : (b : Obj B) → (c : Obj C) → {x y : Obj A} {f : Hom A x y} → _∘_ D ([ ([-, c , c ] G) ]₁ f) (η₁ x b c) ≡ _∘_ D (η₁ y b c) ([ ([-, b , b ] F) ]₁ f)}
  → {ex₀ : (a : Obj A) → (b : Obj B) → {c c' : Obj C} → (f : Hom C c c') → _∘_ D ([ G ]₁ (id A , f , id C)) (η₀ a b c') ≡ _∘_ D ([ G ]₁ (id A , id (C op) , f)) (η₀ a b c)}
  → {ex₁ : (a : Obj A) → (b : Obj B) → {c c' : Obj C} → (f : Hom C c c') → _∘_ D ([ G ]₁ (id A , f , id C)) (η₁ a b c') ≡ _∘_ D ([ G ]₁ (id A , id (C op) , f)) (η₁ a b c)}
  → {exo₀ : (a : Obj A) → (c : Obj C) → {b b' : Obj B} → (f : Hom B b b') → _∘_ D (η₀ a b' c) ([ F ]₁ (id A , id (B op) , f)) ≡ _∘_ D (η₀ a b c) ([ F ]₁ (id A , f , id B))}
  → {exo₁ : (a : Obj A) → (c : Obj C) → {b b' : Obj B} → (f : Hom B b b') → _∘_ D (η₁ a b' c) ([ F ]₁ (id A , id (B op) , f)) ≡ _∘_ D (η₁ a b c) ([ F ]₁ (id A , f , id B))}
  → η₀ ≡ η₁
  → extranatural-transformation {F = F} {G} η₀ nat₀ ex₀ exo₀ ≡ extranatural-transformation {F = F} {G} η₁ nat₁ ex₁ exo₁
extranatural-transformation-eq {F = F} {G} {η} {.η} {nat₀} {nat₁} {ex₀} {ex₁} {exo₀} {exo₁} refl = cong₃ (extranatural-transformation {F = F} {G} η) p1 p2 p3
  where
    p1 : nat₀ ≡ nat₁
    p1 = fun-ext $ λ a → fun-ext $ λ b → implicit-fun-ext 
       $ λ x → implicit-fun-ext $ λ y → implicit-fun-ext 
       $ λ f → proof-irrelevance (nat₀ a b {x} {y} {f}) (nat₁ a b {x} {y} {f})
    
    p2 : ex₀ ≡ ex₁
    p2 = fun-ext $ λ a → fun-ext $ λ b → implicit-fun-ext 
       $ λ c → implicit-fun-ext $ λ c' → fun-ext 
       $ λ f → proof-irrelevance (ex₀ a b f) (ex₁ a b f)
    
    p3 : exo₀ ≡ exo₁
    p3 = fun-ext $ λ a → fun-ext $ λ c → implicit-fun-ext 
       $ λ b → implicit-fun-ext $ λ b' → fun-ext 
       $ λ f → proof-irrelevance (exo₀ a c f) (exo₁ a c f)
