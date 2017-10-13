
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Haskell.Functor hiding ( functor ; functor-eq ) renaming ( Functor to HaskellFunctor )
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.ConstZeroCell

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Properties.FromIndexedMonad where

open Category

IndexedMonad→LaxTwoFunctor
  : {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level}
  → {I : Category {ℓI₀} {ℓI₁}}
  → {C : Category {ℓC₀} {ℓC₁}}
  → {M : {a b : Obj I} → Hom I a b → Functor C C}
  → (monad : IndexedMonad I M)
  → ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C
IndexedMonad→LaxTwoFunctor {ℓI₀} {ℓI₁} {ℓC₀} {ℓC₁} {I} {C} {M} monad = record
  { P₁ = λ {i} {j} → P {i} {j}
  ; η = η'
  ; μ = μ'
  ; laxFunId₁ = laxFunId₁
  ; laxFunId₂ = laxFunId₂
  ; laxFunAssoc = laxFunAssoc
  ; μ-natural₁ = μ-natural₁
  ; μ-natural₂ = μ-natural₂
  }
  where
    I₂ = discreteHomCatTwoCategory I
    Cat' = Cat {ℓC₀} {ℓC₁}

    _∘Cat_ = StrictTwoCategory._∘_ Cat'
    _∘I_ = Category._∘_ I
    _∘C_ = Category._∘_ C

    open IndexedMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    P : {i j : Obj I} → Functor (HomCat I₂ i j) (HomCat Cat' C C)
    P {i} {j} = Functor.functor P₀ P₁ (λ { {f} → refl }) (λ {a b c} {f} {g} → P-compose {a} {b} {c} {f} {g})
      where
        P₀ : Obj (HomCat I₂ i j) → Obj (HomCat Cat' C C)
        P₀ f = M f
        
        P₁ : {a b : Obj (HomCat I₂ i j)} → Hom (HomCat I₂ i j) a b → Hom (HomCat Cat' C C) (P₀ a) (P₀ b)
        P₁ {f} {.f} refl = Id⟨ P₀ f ⟩
        
        abstract
          P-compose : {a b c : Obj (HomCat I₂ i j)} {f : Hom (HomCat I₂ i j) a b} {g : Hom (HomCat I₂ i j) b c}
                    → P₁ (Category._∘_ (HomCat I₂ i j) g f) ≡ ⟨ P₁ g ⟩∘ᵥ⟨ P₁ f ⟩
          P-compose {f} {.f} {.f} {refl} {refl} = sym (left-id (HomCat Cat' C C))

    η' : {x : Cell₀ I₂} → Cell₂ Cat (id₁ Cat) ([ P {x} {x} ]₀ (id₁ I₂))
    η' {i} = η i
    
    μ' : {x y z : Cell₀ I₂}
       → {f : Cell₁ I₂ x y} {g : Cell₁ I₂ y z}
       → Cell₂ Cat ([ P ]₀ g ∘Cat [ P ]₀ f) ([ P ]₀ (g ∘I f))
    μ' {f = f} {g} = μ f g
    
    abstract
      μ-natural₁ : {a b c : Obj I} (f : Hom I a b) {x y : Hom I b c} {α : Cell₂ I₂ x y}
                 → ⟨ [ P ]₁ ((discreteHomCatTwoCategory I ∘ₕ α) (id₂ I₂)) ⟩∘ᵥ⟨ μ f x ⟩
                 ≡ ⟨ μ f y ⟩∘ᵥ⟨ ((Cat ∘ₕ [ P ]₁ α) ([ P ]₁ (id₂ I₂))) ⟩
      μ-natural₁ {a} {b} {c} f {x} {.x} {refl} = trans (StrictTwoCategory.vertical-right-id Cat) 
                                               $ trans (sym (StrictTwoCategory.vertical-left-id Cat)) 
                                               $ cong (λ X → ⟨ μ f x ⟩∘ᵥ⟨ X ⟩) (sym (id∘ₕid≡id Cat))
      
    abstract
      μ-natural₂ : {a b c : Obj I} (g : Hom I b c) {x y : Hom I a b} {α : Cell₂ I₂ x y}
                 → ⟨ [ P ]₁ ((discreteHomCatTwoCategory I ∘ₕ id₂ I₂) α) ⟩∘ᵥ⟨ μ x g ⟩
                 ≡ ⟨ μ y g ⟩∘ᵥ⟨ ⟨ [ P ]₁ (id₂ I₂) ⟩∘ₕ⟨ [ P ]₁ α ⟩ ⟩
      μ-natural₂ {a} {b} {c} g {x} {.x} {refl} = trans (StrictTwoCategory.vertical-right-id Cat) 
                                               $ trans (sym (StrictTwoCategory.vertical-left-id Cat)) 
                                               $ cong (λ X → ⟨ μ x g ⟩∘ᵥ⟨ X ⟩) (sym (id∘ₕid≡id Cat))


    abstract
      laxFunId₁ : {i j : Obj I} {f : Hom I i j}
                → ⟨ μ (id I {i}) f ⟩∘ᵥ⟨ ⟨ Id⟨ M f ⟩ ⟩∘ₕ⟨ η i ⟩ ⟩ 
                ≅ id₂ Cat {C}
      laxFunId₁ {i} {j} {f} = het-natural-transformation-eq (StrictTwoCategory.left-id Cat) (cong M (left-id I)) 
                            $ het-fun-ext (het-fun-ext hrefl $ λ (x : Obj C) → hcong (λ Y → Hom C ([ M f ]₀ x) ([ M Y ]₀ x)) (≡-to-≅ (left-id I))) 
                            $ λ (x : Obj C) → htrans (hcong (λ X → nat-η (μ (id I) f) x ∘C X) (≡-to-≅ (Category.right-id C))) (η-left-coher {i} {j} {f} {x})
    
    abstract
      laxFunId₂ : {i j : Obj I} {f : Hom I i j}
                → ⟨ μ f (id I {j}) ⟩∘ᵥ⟨ ⟨ η j ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ f ⟩ ⟩ ⟩ 
                ≅ id₂ Cat' {C}
      laxFunId₂ {i} {j} {f} = het-natural-transformation-eq (StrictTwoCategory.right-id Cat) (cong M (right-id I)) 
                            $ het-fun-ext (het-fun-ext hrefl $ (λ (x : Obj C) → hcong (λ Y → Hom C ([ M f ]₀ x) ([ M Y ]₀ x)) (≡-to-≅ (right-id I)))) 
                            $ λ (x : Obj C) → htrans (hcong (λ X → nat-η (μ f (id I)) x ∘C X) (≡-to-≅ (Category.left-id C))) (η-right-coher {i} {j} {f} {x})
    
    abstract
      laxFunAssoc : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l}
                  → ⟨ μ (g ∘I f) h ⟩∘ᵥ⟨ ⟨ Id⟨ M h ⟩ ⟩∘ₕ⟨ μ f g ⟩ ⟩
                  ≅ ⟨ μ f (h ∘I g) ⟩∘ᵥ⟨ ⟨ μ g h ⟩∘ₕ⟨ Id⟨ M f ⟩ ⟩ ⟩
      laxFunAssoc {i} {j} {k} {l} {f} {g} {h} = het-natural-transformation-eq (StrictTwoCategory.assoc Cat) (cong M (assoc I))  
                                              $ het-fun-ext (het-fun-ext hrefl $ λ (x : Obj C) → hcong (λ Y → Hom C ([ [ M h ]∘[ [ M g ]∘[ M f ] ] ]₀ x) ([ M Y ]₀ x)) (≡-to-≅ (assoc I))) 
                                              $ λ (x : Obj C) → htrans (hcong (λ X → nat-η (μ (g ∘I f) h) x ∘C X) (≡-to-≅ $ Category.right-id C)) 
                                              $ htrans μ-coher
                                              $ hcong (λ X → nat-η (μ f (h ∘I g)) x ∘C X) $ hsym 
                                              $ htrans (hcong (λ X → nat-η (μ g h) ([ M f ]₀ x) ∘C X) (≡-to-≅ $ Functor.id ([ M h ]∘[ M g ]))) (≡-to-≅ $ Category.left-id C)
