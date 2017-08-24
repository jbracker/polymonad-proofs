 
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

open Category hiding ( left-id ; right-id ; assoc ;_∘_ ) renaming ( id to idC )
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
    
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C

    _∘Cₕ_ = _∘ₕ_ C
    _∘Dₕ_ = _∘ₕ_ D

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
         → Cell₂ D ([ P₁ ]₀ g  ∘D  [ P₁ ]₀ f) ([ P₁ ]₀ (g ∘C f))
    
    laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
                → ([ P₁ {w} {z} ]₁ (α C f g h)) 
                  ∘Dᵥ ( (μ {w} {y} {z} {g ∘C f} {h}) 
                  ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ μ {w} {x} {y} {f} {g}) ) 
                ≡ μ {w} {x} {z} {f} {h ∘C g} 
                  ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
                  ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
               -- P₂ α ∘ᵥ μ ∘ᵥ (id₂ ∘ₕ μ) ≡ μ ∘ᵥ (μ ∘ₕ id₂) ∘ᵥ α P₁
    
    μ-natural₁ : {a b c : Cell₀ C} → (f : Cell₁ C a b) → {x y : Cell₁ C b c} {α : Cell₂ C x y} 
               → [ P₁ ]₁ (α ∘Cₕ id₂ C {a}) ∘Dᵥ μ {f = f} {x} ≡ μ {f = f} {y} ∘Dᵥ ([ P₁ ]₁ α ∘Dₕ [ P₁ ]₁ (id₂ C {a}))
    
    μ-natural₂ : {a b c : Cell₀ C} → (g : Cell₁ C b c) {x y : Cell₁ C a b} {α : Cell₂ C x y}
               → [ P₁ ]₁ (id₂ C {b} ∘Cₕ α) ∘Dᵥ μ {f = x} {g} ≡ μ {f = y} {g} ∘Dᵥ ([ P₁ ]₁ (id₂ C {b}) ∘Dₕ [ P₁ ]₁ α)
  
  FL : {a b c : Cell₀ C} → Functor (HomCat C a b ×C HomCat C b c) (HomCat D (P₀ a) (P₀ c))
  FL {a} {b} {c} = functor FL₀ FL₁ FL-id FL-compose
    where
      FL₀ : Obj (HomCat C a b ×C HomCat C b c) → Obj (HomCat D (P₀ a) (P₀ c))
      FL₀ (f , g) = [ P₁ ]₀ g ∘D [ P₁ ]₀ f
      
      FL₁ : {x y : Obj (HomCat C a b ×C HomCat C b c)} 
          → Hom (HomCat C a b ×C HomCat C b c) x y 
          → Hom (HomCat D (P₀ a) (P₀ c)) (FL₀ x) (FL₀ y)
      FL₁ {x} {y} (f , g) = [ P₁ ]₁ g ∘Dₕ [ P₁ ]₁ f
      
      abstract
        FL-id : {x : Obj (HomCat C a b ×C HomCat C b c)}
              → FL₁ (idC (HomCat C a b ×C HomCat C b c) {x}) ≡ idC (HomCat D (P₀ a) (P₀ c)) {FL₀ x}
        FL-id {x , y} = begin
          [ P₁ ]₁ (idC (HomCat C b c) {y}) ∘Dₕ [ P₁ ]₁ (idC (HomCat C a b) {x})
            ≡⟨ cong₂ _∘Dₕ_ (Functor.id P₁) (Functor.id P₁) ⟩
          idC (HomCat D (P₀ b) (P₀ c)) {[ P₁ ]₀ y} ∘Dₕ idC (HomCat D (P₀ a) (P₀ b)) {[ P₁ ]₀ x}
            ≡⟨ id∘ₕid≡id D ⟩
          idC (HomCat D (P₀ a) (P₀ c)) {[ P₁ ]₀ y ∘D [ P₁ ]₀ x} ∎
      
      abstract
        FL-compose : {x y z : Obj (HomCat C a b ×C HomCat C b c)}
                   → {f : Hom (HomCat C a b ×C HomCat C b c) x y} {g : Hom (HomCat C a b ×C HomCat C b c) y z}
                   → FL₁ (Category._∘_ (HomCat C a b ×C HomCat C b c) g f) ≡ (FL₁ g) ∘Dᵥ (FL₁ f)
        FL-compose {x , x'} {y , y'} {z , z'} {f , f'} {g , g'} = begin
          [ P₁ ]₁ (g' ∘Cᵥ f') ∘Dₕ [ P₁ ]₁ (g ∘Cᵥ f)
            ≡⟨ cong₂ _∘Dₕ_ (Functor.compose P₁) (Functor.compose P₁) ⟩
          ([ P₁ ]₁ g' ∘Dᵥ [ P₁ ]₁ f') ∘Dₕ ([ P₁ ]₁ g ∘Dᵥ [ P₁ ]₁ f)
            ≡⟨ interchange D ([ P₁ ]₁ f) ([ P₁ ]₁ f') ([ P₁ ]₁ g) ([ P₁ ]₁ g') ⟩
          ([ P₁ ]₁ g' ∘Dₕ [ P₁ ]₁ g) ∘Dᵥ ([ P₁ ]₁ f' ∘Dₕ [ P₁ ]₁ f) ∎
        
  FR : {a b c : Cell₀ C} → Functor (HomCat C a b ×C HomCat C b c) (HomCat D (P₀ a) (P₀ c))
  FR {a} {b} {c} = functor FR₀ FR₁ FR-id FR-compose
    where
      FR₀ : Obj (HomCat C a b ×C HomCat C b c) → Obj (HomCat D (P₀ a) (P₀ c))
      FR₀ (f , g) = [ P₁ ]₀ (g ∘C f)
      
      FR₁ : {x y : Obj (HomCat C a b ×C HomCat C b c)} 
          → Hom (HomCat C a b ×C HomCat C b c) x y 
          → Hom (HomCat D (P₀ a) (P₀ c)) (FR₀ x) (FR₀ y)
      FR₁ {x} {y} (f , g) = [ P₁ ]₁ (g ∘Cₕ f)
      
      abstract
        FR-id : {x : Obj (HomCat C a b ×C HomCat C b c)}
              → FR₁ (idC (HomCat C a b ×C HomCat C b c) {x}) ≡ idC (HomCat D (P₀ a) (P₀ c)) {FR₀ x}
        FR-id {x , y} = begin
          [ P₁ ]₁ (idC (HomCat C b c) {y} ∘Cₕ idC (HomCat C a b) {x})
            ≡⟨ cong (λ X → [ P₁ ]₁ X) (id∘ₕid≡id C) ⟩
          [ P₁ ]₁ (idC (HomCat C a c) {y ∘C x})
            ≡⟨ Functor.id P₁ ⟩
          idC (HomCat D (P₀ a) (P₀ c)) {[ P₁ ]₀ (y ∘C x)} ∎
      
      abstract
        FR-compose : {x y z : Obj (HomCat C a b ×C HomCat C b c)}
                   → {f : Hom (HomCat C a b ×C HomCat C b c) x y} {g : Hom (HomCat C a b ×C HomCat C b c) y z}
                   → FR₁ (Category._∘_ (HomCat C a b ×C HomCat C b c) g f) ≡ (FR₁ g) ∘Dᵥ (FR₁ f)
        FR-compose {x , x'} {y , y'} {z , z'} {f , f'} {g , g'} = begin
          [ P₁ ]₁ ((g' ∘Cᵥ f') ∘Cₕ (g ∘Cᵥ f))
            ≡⟨ cong (λ X → [ P₁ ]₁ X) (interchange C f f' g g') ⟩
          [ P₁ ]₁ ((g' ∘Cₕ g) ∘Cᵥ (f' ∘Cₕ f))
            ≡⟨ Functor.compose P₁ ⟩
          [ P₁ ]₁ (g' ∘Cₕ g) ∘Dᵥ [ P₁ ]₁ (f' ∘Cₕ f) ∎

  open Theory.Functor.Application.BiFunctor
  
  μ-natural-transformation₁ : {a b c : Cell₀ C} → (f : Obj (HomCat C a b)) 
                            → NaturalTransformation ([ f ,-] (FL {a} {b} {c})) ([ f ,-] (FR {a} {b} {c}))
  μ-natural-transformation₁ {a} {b} {c} f = naturalTransformation (λ g → μ {f = f} {g}) (μ-natural₁ {a} {b} {c} f)

  μ-natural-transformation₂ : {a b c : Cell₀ C} → (g : Obj (HomCat C b c)) 
                            → NaturalTransformation ([-, g ] (FL {a} {b} {c})) ([-, g ] (FR {a} {b} {c}))
  μ-natural-transformation₂ {a} {b} {c} g = naturalTransformation (λ f → μ {f = f} {g}) (μ-natural₂ {a} {b} {c} g)
