 
module Theory.TwoFunctor.Definition where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ )

-- Local
open import Utilities
open import Extensionality
open import Congruence
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Examples
open import Theory.Functor.Application
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.CodiscreteHomCat

-------------------------------------------------------------------------------
-- Definition of 2-Functors
-------------------------------------------------------------------------------

open Category hiding ( left-id ; right-id ; assoc ) renaming ( id to idC )
open StrictTwoCategory

record LaxTwoFunctor {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                     (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) 
                     (D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}) 
                     : Set (lsuc (ℓC₀ ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓD₂)) where
  constructor lax-two-functor

  private
    _▷D_ = _▷_ D
    _▷C_ = _▷_ C

    _◁D_ = _◁_ D
    _◁C_ = _◁_ C
    
    _∘Dₕ_ = _∘ₕ_ D
    _∘Cₕ_ = _∘ₕ_ C

    _∘Cₕ₂_ = _∘ₕ₂_ C
    _∘Dₕ₂_ = _∘ₕ₂_ D

    _∘Dᵥ_ = _∘ᵥ_ D
    _∘Cᵥ_ = _∘ᵥ_ C

    id₁D = id₁ D

  field
    -- Names and structure base on: https://ncatlab.org/nlab/show/pseudofunctor
    -- Of course, adapted to lax 2-functors.
    
    -- P_{x}
    P₀ : Cell₀ C → Cell₀ D
    -- P_{x,y}
    P₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D (P₀ x) (P₀ y))
    
    -- P_{id_x}
    η : {x : Cell₀ C}
      → Cell₂ D (id₁ D {P₀ x}) ([ P₁ {x} {x} ]₀ (id₁ C {x}))

    -- P_{x,y,z}
    μ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z}
         -- (F₁ g ∘ F₁ f) ∼ F₁ (g ∘ f)
         → Cell₂ D ([ P₁ ]₀ g  ∘Dₕ  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘Cₕ f))
    
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
                → ([ P₁ {w} {z} ]₁ (α C f g h)) 
                  ∘Dᵥ ( (μ {w} {y} {z} {g ∘Cₕ f} {h}) 
                  ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ₂ μ {w} {x} {y} {f} {g}) ) 
                ≡ μ {w} {x} {z} {f} {h ∘Cₕ g} 
                  ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ₂ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
                  ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
               -- P₂ α ∘ᵥ μ ∘ᵥ (id₂ ∘ₕ μ) ≡ μ ∘ᵥ (μ ∘ₕ id₂) ∘ᵥ α P₁
    
    μ-natural₁ : {a b c : Cell₀ C} → (f : Cell₁ C a b) → {x y : Cell₁ C b c} {α : Cell₂ C x y} 
               → [ P₁ ]₁ (α ∘Cₕ₂ id₂ C {a}) ∘Dᵥ μ {f = f} {x} ≡ μ {f = f} {y} ∘Dᵥ ([ P₁ ]₁ α ∘Dₕ₂ [ P₁ ]₁ (id₂ C {a}))
    
    μ-natural₂ : {a b c : Cell₀ C} → (g : Cell₁ C b c) {x y : Cell₁ C a b} {α : Cell₂ C x y}
               → [ P₁ ]₁ (id₂ C {b} ∘Cₕ₂ α) ∘Dᵥ μ {f = x} {g} ≡ μ {f = y} {g} ∘Dᵥ ([ P₁ ]₁ (id₂ C {b}) ∘Dₕ₂ [ P₁ ]₁ α)
  
  FL : {a b c : Cell₀ C} → Functor (HomCat C a b ×C HomCat C b c) (HomCat D (P₀ a) (P₀ c))
  FL {a} {b} {c} = functor FL₀ FL₁ FL-id FL-compose
    where
      FL₀ : Obj (HomCat C a b ×C HomCat C b c) → Obj (HomCat D (P₀ a) (P₀ c))
      FL₀ (f , g) = [ P₁ ]₀ g ∘Dₕ [ P₁ ]₀ f
      
      FL₁ : {x y : Obj (HomCat C a b ×C HomCat C b c)} 
          → Hom (HomCat C a b ×C HomCat C b c) x y 
          → Hom (HomCat D (P₀ a) (P₀ c)) (FL₀ x) (FL₀ y)
      FL₁ {x} {y} (f , g) = [ P₁ ]₁ g ∘Dₕ₂ [ P₁ ]₁ f
      
      abstract
        FL-id : {x : Obj (HomCat C a b ×C HomCat C b c)}
              → FL₁ (idC (HomCat C a b ×C HomCat C b c) {x}) ≡ idC (HomCat D (P₀ a) (P₀ c)) {FL₀ x}
        FL-id {x , y} = begin
          [ P₁ ]₁ (idC (HomCat C b c) {y}) ∘Dₕ₂ [ P₁ ]₁ (idC (HomCat C a b) {x})
            ≡⟨ cong₂ _∘Dₕ₂_ (Functor.id P₁) (Functor.id P₁) ⟩
          idC (HomCat D (P₀ b) (P₀ c)) {[ P₁ ]₀ y} ∘Dₕ₂ idC (HomCat D (P₀ a) (P₀ b)) {[ P₁ ]₀ x}
            ≡⟨ id∘ₕ₂id≡id D ⟩
          idC (HomCat D (P₀ a) (P₀ c)) {[ P₁ ]₀ y ∘Dₕ [ P₁ ]₀ x} ∎
      
      abstract
        FL-compose : {x y z : Obj (HomCat C a b ×C HomCat C b c)}
                   → {f : Hom (HomCat C a b ×C HomCat C b c) x y} {g : Hom (HomCat C a b ×C HomCat C b c) y z}
                   → FL₁ (((HomCat C a b ×C HomCat C b c) ∘ g) f) ≡ (HomCat D (P₀ a) (P₀ c) ∘ FL₁ g) (FL₁ f)
        FL-compose {x , x'} {y , y'} {z , z'} {f , f'} {g , g'} = begin
          [ P₁ ]₁ (g' ∘Cᵥ f') ∘Dₕ₂ [ P₁ ]₁ (g ∘Cᵥ f)
            ≡⟨ cong₂ _∘Dₕ₂_ (Functor.compose P₁) (Functor.compose P₁) ⟩
          ([ P₁ ]₁ g' ∘Dᵥ [ P₁ ]₁ f') ∘Dₕ₂ ([ P₁ ]₁ g ∘Dᵥ [ P₁ ]₁ f)
            ≡⟨ interchange D ([ P₁ ]₁ f) ([ P₁ ]₁ f') ([ P₁ ]₁ g) ([ P₁ ]₁ g') ⟩
          ([ P₁ ]₁ g' ∘Dₕ₂ [ P₁ ]₁ g) ∘Dᵥ ([ P₁ ]₁ f' ∘Dₕ₂ [ P₁ ]₁ f) ∎
        
  FR : {a b c : Cell₀ C} → Functor (HomCat C a b ×C HomCat C b c) (HomCat D (P₀ a) (P₀ c))
  FR {a} {b} {c} = functor FR₀ FR₁ FR-id FR-compose
    where
      FR₀ : Obj (HomCat C a b ×C HomCat C b c) → Obj (HomCat D (P₀ a) (P₀ c))
      FR₀ (f , g) = [ P₁ ]₀ (g ∘Cₕ f)
      
      FR₁ : {x y : Obj (HomCat C a b ×C HomCat C b c)} 
          → Hom (HomCat C a b ×C HomCat C b c) x y 
          → Hom (HomCat D (P₀ a) (P₀ c)) (FR₀ x) (FR₀ y)
      FR₁ {x} {y} (f , g) = [ P₁ ]₁ (g ∘Cₕ₂ f)
      
      abstract
        FR-id : {x : Obj (HomCat C a b ×C HomCat C b c)}
              → FR₁ (idC (HomCat C a b ×C HomCat C b c) {x}) ≡ idC (HomCat D (P₀ a) (P₀ c)) {FR₀ x}
        FR-id {x , y} = begin
          [ P₁ ]₁ (idC (HomCat C b c) {y} ∘Cₕ₂ idC (HomCat C a b) {x})
            ≡⟨ cong (λ X → [ P₁ ]₁ X) (id∘ₕ₂id≡id C) ⟩
          [ P₁ ]₁ (idC (HomCat C a c) {y ∘Cₕ x})
            ≡⟨ Functor.id P₁ ⟩
          idC (HomCat D (P₀ a) (P₀ c)) {[ P₁ ]₀ (y ∘Cₕ x)} ∎
      
      abstract
        FR-compose : {x y z : Obj (HomCat C a b ×C HomCat C b c)}
                   → {f : Hom (HomCat C a b ×C HomCat C b c) x y} {g : Hom (HomCat C a b ×C HomCat C b c) y z}
                   → FR₁ (((HomCat C a b ×C HomCat C b c) ∘ g) f) ≡ (HomCat D (P₀ a) (P₀ c) ∘ FR₁ g) (FR₁ f)
        FR-compose {x , x'} {y , y'} {z , z'} {f , f'} {g , g'} = begin
          [ P₁ ]₁ ((g' ∘Cᵥ f') ∘Cₕ₂ (g ∘Cᵥ f))
            ≡⟨ cong (λ X → [ P₁ ]₁ X) (interchange C f f' g g') ⟩
          [ P₁ ]₁ ((g' ∘Cₕ₂ g) ∘Cᵥ (f' ∘Cₕ₂ f))
            ≡⟨ Functor.compose P₁ ⟩
          [ P₁ ]₁ (g' ∘Cₕ₂ g) ∘Dᵥ [ P₁ ]₁ (f' ∘Cₕ₂ f) ∎

  open Theory.Functor.Application.BiFunctor
  
  μ-natural-transformation₁ : {a b c : Cell₀ C} → (f : Obj (HomCat C a b)) 
                            → NaturalTransformation ([ f ,-] (FL {a} {b} {c})) ([ f ,-] (FR {a} {b} {c}))
  μ-natural-transformation₁ {a} {b} {c} f = naturalTransformation (λ g → μ {f = f} {g}) (μ-natural₁ {a} {b} {c} f)

  μ-natural-transformation₂ : {a b c : Cell₀ C} → (g : Obj (HomCat C b c)) 
                            → NaturalTransformation ([-, g ] (FL {a} {b} {c})) ([-, g ] (FR {a} {b} {c}))
  μ-natural-transformation₂ {a} {b} {c} g = naturalTransformation (λ f → μ {f = f} {g}) (μ-natural₂ {a} {b} {c} g)

-------------------------------------------------------------------------------
-- Creating a Lax 2-Functor from a Functor.
-------------------------------------------------------------------------------

Functor→LaxTwoFunctor : ∀ {ℓ₀ ℓ₁} {C D : Category {ℓ₀} {ℓ₁}} 
                      → Functor C D → LaxTwoFunctor (codiscreteHomCatTwoCategory C) (codiscreteHomCatTwoCategory D)
Functor→LaxTwoFunctor {ℓ₀} {ℓ₁} {C} {D} F = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = lift tt
  ; μ = lift tt
  ; laxFunId₁ = refl
  ; laxFunId₂ = refl
  ; laxFunAssoc = refl
  ; μ-natural₁ = λ f → refl
  ; μ-natural₂ = λ g → refl
  } where
      C' = codiscreteHomCatTwoCategory C
      D' = codiscreteHomCatTwoCategory D
      
      P₀ : Cell₀ C' → Cell₀ D'
      P₀ a = [ F ]₀ a
      
      P₁ : {x y : Cell₀ C'} → Functor (HomCat C' x y) (HomCat D' (P₀ x) (P₀ y))
      P₁ {x} {y} = record 
        { F₀ = F₀
        ; F₁ = λ {a} {b} → F₁ {a} {b}
        ; id = refl
        ; compose = refl
        } where
          F₀ : Obj (HomCat C' x y) → Obj (HomCat D' (P₀ x) (P₀ y))
          F₀ f = [ F ]₁ f
          
          F₁ : {a b : Obj (HomCat C' x y)} 
             → Hom (HomCat C' x y) a b → Hom (HomCat D' (P₀ x) (P₀ y)) (F₀ a) (F₀ b)
          F₁ f = lift tt
