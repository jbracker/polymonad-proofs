
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; proof-irrelevance to het-proof-irrelevance )

open import Congruence
open import Extensionality
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell

open Category hiding ( _∘_ )
open StrictTwoCategory

module Theory.TwoFunctor.ConstZeroCell.Equality where

abstract
  const-lax-two-functor-eq : {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level} 
                           → {C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}} 
                           → {D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}} 
                           → {constD : Cell₀ D}
                           → {P₁₀ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D constD constD)}
                           → {P₁₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D constD constD)}
                           → {η₀ : {x : Cell₀ C} → Cell₂ D (id₁ D {constD}) ([ P₁₀ {x} {x} ]₀ (id₁ C {x}))}
                           → {η₁ : {x : Cell₀ C} → Cell₂ D (id₁ D {constD}) ([ P₁₁ {x} {x} ]₀ (id₁ C {x}))}
                           → {μ₀ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z} → Cell₂ D (_∘_ D ([ P₁₀ ]₀ g) ([ P₁₀ ]₀ f)) ([ P₁₀ ]₀ (_∘_ C g f))}
                           → {μ₁ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z} → Cell₂ D (_∘_ D ([ P₁₁ ]₀ g) ([ P₁₁ ]₀ f)) ([ P₁₁ ]₀ (_∘_ C g f))}
                           → {lfi₁₀ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₀ {x} {y} ]₁ (λ' C f)) (_∘ᵥ_ D (μ₀ {x} {x} {y} {id₁ C {x}} {f}) (_∘ₕ_ D (id₂ D {f = [ P₁₀ {x} {y} ]₀ f}) (η₀ {x})) ) ≡ λ' D ([ P₁₀ {x} {y} ]₀ f)}
                           → {lfi₁₁ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₁ {x} {y} ]₁ (λ' C f)) (_∘ᵥ_ D (μ₁ {x} {x} {y} {id₁ C {x}} {f}) (_∘ₕ_ D (id₂ D {f = [ P₁₁ {x} {y} ]₀ f}) (η₁ {x})) ) ≡ λ' D ([ P₁₁ {x} {y} ]₀ f)}
                           → {lfi₂₀ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₀ {x} {y} ]₁ (ρ C f)) (_∘ᵥ_ D (μ₀ {x} {y} {y} {f} {id₁ C {y}}) (_∘ₕ_ D (η₀ {y}) (id₂ D {f = [ P₁₀ {x} {y} ]₀ f})) ) ≡ ρ D ([ P₁₀ {x} {y} ]₀ f)}
                           → {lfi₂₁ : {x y : Cell₀ C} {f : Cell₁ C x y} → _∘ᵥ_ D ([ P₁₁ {x} {y} ]₁ (ρ C f)) (_∘ᵥ_ D (μ₁ {x} {y} {y} {f} {id₁ C {y}}) (_∘ₕ_ D (η₁ {y}) (id₂ D {f = [ P₁₁ {x} {y} ]₀ f})) ) ≡ ρ D ([ P₁₁ {x} {y} ]₀ f)}
                           → {la₀ : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z} 
                                  → _∘ᵥ_ D ([ P₁₀ {w} {z} ]₁ (α C f g h)) (_∘ᵥ_ D (μ₀ {w} {y} {z} {_∘_ C g f} {h}) (_∘ₕ_ D (id₂ D {constD} {constD} {[ P₁₀ {y} {z} ]₀ h}) (μ₀ {w} {x} {y} {f} {g})) ) 
                                  ≡ _∘ᵥ_ D (μ₀ {w} {x} {z} {f} {_∘_ C h g}) 
                                           (_∘ᵥ_ D (_∘ₕ_ D (μ₀ {x} {y} {z} {g} {h}) (id₂ D {constD} {constD} {[ P₁₀ {w} {x} ]₀ f})) (α D ([ P₁₀ {w} {x} ]₀ f) ([ P₁₀ {x} {y} ]₀ g) ([ P₁₀ {y} {z} ]₀ h)) )}
                           → {la₁ : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z} 
                                  → _∘ᵥ_ D ([ P₁₁ {w} {z} ]₁ (α C f g h)) (_∘ᵥ_ D (μ₁ {w} {y} {z} {_∘_ C g f} {h}) (_∘ₕ_ D (id₂ D {constD} {constD} {[ P₁₁ {y} {z} ]₀ h}) (μ₁ {w} {x} {y} {f} {g})) ) 
                                  ≡ _∘ᵥ_ D (μ₁ {w} {x} {z} {f} {_∘_ C h g}) 
                                           (_∘ᵥ_ D (_∘ₕ_ D (μ₁ {x} {y} {z} {g} {h}) (id₂ D {constD} {constD} {[ P₁₁ {w} {x} ]₀ f})) (α D ([ P₁₁ {w} {x} ]₀ f) ([ P₁₁ {x} {y} ]₀ g) ([ P₁₁ {y} {z} ]₀ h)) )}
                           → {μnat₁₀ : {a b c : Cell₀ C} → (f : Cell₁ C a b) → {x y : Cell₁ C b c} {α : Cell₂ C x y} 
                                     → _∘ᵥ_ D ([ P₁₀ ]₁ (_∘ₕ_ C α (id₂ C {a}))) (μ₀ {f = f} {x}) ≡ _∘ᵥ_ D (μ₀ {f = f} {y}) (_∘ₕ_ D ([ P₁₀ ]₁ α) ([ P₁₀ ]₁ (id₂ C {a})))}
                           → {μnat₁₁ : {a b c : Cell₀ C} → (f : Cell₁ C a b) → {x y : Cell₁ C b c} {α : Cell₂ C x y} 
                                     → _∘ᵥ_ D ([ P₁₁ ]₁ (_∘ₕ_ C α (id₂ C {a}))) (μ₁ {f = f} {x}) ≡ _∘ᵥ_ D (μ₁ {f = f} {y}) (_∘ₕ_ D ([ P₁₁ ]₁ α) ([ P₁₁ ]₁ (id₂ C {a})))}
                           → {μnat₂₀ : {a b c : Cell₀ C} → (g : Cell₁ C b c) {x y : Cell₁ C a b} {α : Cell₂ C x y}
                                     → _∘ᵥ_ D ([ P₁₀ ]₁ (_∘ₕ_ C (id₂ C {b}) α)) (μ₀ {f = x} {g}) ≡ _∘ᵥ_ D (μ₀ {f = y} {g}) (_∘ₕ_ D ([ P₁₀ ]₁ (id₂ C {b})) ([ P₁₀ ]₁ α))}
                           → {μnat₂₁ : {a b c : Cell₀ C} → (g : Cell₁ C b c) {x y : Cell₁ C a b} {α : Cell₂ C x y}
                                     → _∘ᵥ_ D ([ P₁₁ ]₁ (_∘ₕ_ C (id₂ C {b}) α)) (μ₁ {f = x} {g}) ≡ _∘ᵥ_ D (μ₁ {f = y} {g}) (_∘ₕ_ D ([ P₁₁ ]₁ (id₂ C {b})) ([ P₁₁ ]₁ α))}
                           → (eqP : (λ {x} {y} → P₁₀ {x} {y}) ≡ P₁₁)
                           → (eq-η : (λ {x} → η₀ {x}) ≅ (λ {x} → η₁ {x}))
                           → (eq-μ : (λ {x} {y} {z} {f} {g} → μ₀ {x} {y} {z} {f} {g}) ≅ (λ {x} {y} {z} {f} {g} → μ₁ {x} {y} {z} {f} {g}))
                           → const-lax-two-functor {C = C} {D} {constD} P₁₀ η₀ μ₀ lfi₁₀ lfi₂₀ la₀ μnat₁₀ μnat₂₀ ≡ const-lax-two-functor {C = C} {D} {constD} P₁₁ η₁ μ₁ lfi₁₁ lfi₂₁ la₁ μnat₁₁ μnat₂₁
  const-lax-two-functor-eq {C = C} {D} {constD} {P₁} {.P₁} {η} {.η} {μ} {.μ} {lfi₁₀} {lfi₁₁} {lfi₂₀} {lfi₂₁} {la₀} {la₁} {μnat₁₀} {μnat₁₁} {μnat₂₀} {μnat₂₁} refl hrefl hrefl 
    = cong₅ (const-lax-two-functor {C = C} {D} {constD} P₁ η μ) p1 p2 p3 p4 p5
    where
      abstract
        p1 : (λ {x} {y} {f} → lfi₁₀ {x} {y} {f}) ≡ lfi₁₁
        p1 = implicit-fun-ext 
           $ λ x → implicit-fun-ext 
           $ λ y → implicit-fun-ext 
           $ λ f → proof-irrelevance (lfi₁₀ {x} {y} {f}) (lfi₁₁ {x} {y} {f})
      
      abstract
        p2 : (λ {x} {y} {f} → lfi₂₀ {x} {y} {f}) ≡ lfi₂₁
        p2 = implicit-fun-ext 
           $ λ x → implicit-fun-ext 
           $ λ y → implicit-fun-ext 
           $ λ f → proof-irrelevance (lfi₂₀ {x} {y} {f}) (lfi₂₁ {x} {y} {f})
      
      abstract
        p3 : (λ {w} {x} {y} {z} {f} {g} {h} → la₀ {w} {x} {y} {z} {f} {g} {h}) ≡ la₁
        p3 = implicit-fun-ext 
           $ λ w → implicit-fun-ext 
           $ λ x → implicit-fun-ext 
           $ λ y → implicit-fun-ext 
           $ λ z → implicit-fun-ext 
           $ λ f → implicit-fun-ext 
           $ λ g → implicit-fun-ext 
           $ λ h → proof-irrelevance (la₀ {w} {x} {y} {z} {f} {g} {h}) (la₁ {w} {x} {y} {z} {f} {g} {h})
      
      abstract
        p4 : (λ {a b c} → μnat₁₀ {a} {b} {c}) ≡ μnat₁₁
        p4 = implicit-fun-ext 
           $ λ a → implicit-fun-ext 
           $ λ b → implicit-fun-ext 
           $ λ c → fun-ext 
           $ λ f → implicit-fun-ext 
           $ λ x → implicit-fun-ext 
           $ λ y → implicit-fun-ext 
           $ λ α → proof-irrelevance (μnat₁₀ {a} {b} {c} f {x} {y} {α}) (μnat₁₁ {a} {b} {c} f {x} {y} {α}) 
      
      abstract
        p5 : (λ {a b c} → μnat₂₀ {a} {b} {c}) ≡ μnat₂₁
        p5 = implicit-fun-ext 
           $ λ a → implicit-fun-ext 
           $ λ b → implicit-fun-ext 
           $ λ c → fun-ext 
           $ λ g → implicit-fun-ext 
           $ λ x → implicit-fun-ext 
           $ λ y → implicit-fun-ext 
           $ λ α → proof-irrelevance (μnat₂₀ {a} {b} {c} g {x} {y} {α}) (μnat₂₁ {a} {b} {c} g {x} {y} {α})

    
    
    
    
    
    
 
