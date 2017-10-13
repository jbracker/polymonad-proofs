
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
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
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

module Theory.TwoFunctor.Properties.ToIndexedMonad where

LaxTwoFunctor→IndexedMonad
  : {ℓI₀ ℓI₁ ℓC₀ ℓC₁ : Level}
  → {I : Category {ℓI₀} {ℓI₁}}
  → {C : Category {ℓC₀} {ℓC₁}}
  → (F : ConstLaxTwoFunctor (discreteHomCatTwoCategory I) (Cat {ℓC₀} {ℓC₁}) C)
  → IndexedMonad I (λ {i j} f → [ ConstLaxTwoFunctor.P₁ F {i} {j} ]₀ f)
LaxTwoFunctor→IndexedMonad {ℓI₀} {ℓI₁} {ℓC₀} {ℓC₁} {I} {C} F = indexed-monad η' μ' assoc' left-id' right-id'
  where
    open ConstLaxTwoFunctor F
    open NaturalTransformation renaming (η to nat-η)
    
    I₂ = discreteHomCatTwoCategory I
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    _∘C_ = Category._∘_ C
    _∘I_ = Category._∘_ I
    
    _∘ᵥCat_ = _∘ᵥ_ Cat'
    _∘ₕCat_ = _∘ₕ_ Cat'
    
    M : {i j : Obj I} → Hom I i j → Functor C C
    M {i} {j} f = [ P₁ {i} {j} ]₀ f
    
    η' : (i : Obj I) → NaturalTransformation Id[ C ] ([ P₁ ]₀ (id I))
    η' i = ConstLaxTwoFunctor.η F {i}
    
    μ' : {i j k : Obj I} (f : Hom I i j) (g : Hom I j k) → NaturalTransformation [ [ P₁ ]₀ g ]∘[ [ P₁ ]₀ f ] ([ P₁ ]₀ (g ∘I f))
    μ' f g = ConstLaxTwoFunctor.μ F {f = f} {g = g}
    
    abstract
      nat-eq : {F G H I : Functor C C} → {α : NaturalTransformation F G} {β : NaturalTransformation H I}
             → F ≡ H → G ≡ I → α ≅ β → (x : Obj C) 
             → nat-η α x ≅ nat-η β x
      nat-eq refl refl hrefl x = hrefl
    
    abstract
      assoc' : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Obj C}
             → nat-η (μ' (g ∘I f) h) x ∘C [ M h ]₁ (nat-η (μ' f g) x) 
             ≅ nat-η (μ' f (h ∘I g)) x ∘C nat-η (μ' g h) ([ M f ]₀ x)
      assoc' {i} {j} {k} {l} {f} {g} {h} {x} = hbegin
        nat-η (μ' (g ∘I f) h) x ∘C [ M h ]₁ (nat-η (μ' f g) x) 
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ' (g ∘I f) h) x ∘C X) (sym (Category.right-id C)) ⟩
        nat-η (μ' (g ∘I f) h) x ∘C (id C {[ [ M h ]∘[ M (g ∘I f) ] ]₀ x} ∘C [ M h ]₁ (nat-η (μ' f g) x)) 
          ≅⟨ hrefl ⟩
        nat-η (μ' (g ∘I f) h ∘ᵥCat (id₂ Cat ∘ₕCat μ' f g)) x
          ≅⟨ nat-eq {α = μ' (g ∘I f) h ∘ᵥCat (id₂ Cat ∘ₕCat μ' f g)} 
                    {β = μ' f (h ∘I g) ∘ᵥCat (μ' g h ∘ₕCat (id₂ Cat))} 
                    (functor-eq refl hrefl) 
                    (functor-eq ( cong (λ X → Functor.F₀ ([ P₁ ]₀ X)) (assoc I)) $ het-implicit-fun-ext (het-fun-ext hrefl $ λ (a : Obj C) → hcong (λ X → ({b : Obj C} → Hom C a b 
                                                                                                                                                        → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b))) 
                                                                                                                                                   (≡-to-≅ (assoc I))) 
                                $ λ (a : Obj C) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (b : Obj C) → hcong (λ X → Hom C a b 
                                                                                                                       → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                                  (≡-to-≅ (assoc I))) 
                                $ λ (b : Obj C) → het-fun-ext (het-fun-ext hrefl $ λ (f : Hom C a b) → hcong (λ X → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                             (≡-to-≅ (assoc I))) 
                                $ λ (f : Hom C a b) → hcong (λ X → Functor.F₁ (Functor.F₀ P₁ X) f) (≡-to-≅ (assoc I)) )
                    laxFunAssoc
                    x ⟩
        nat-η (μ' f (h ∘I g) ∘ᵥCat (μ' g h ∘ₕCat (id₂ Cat))) x
          ≅⟨ hrefl ⟩
        nat-η (μ' f (h ∘I g)) x ∘C (nat-η (μ' g h) ([ M f ]₀ x) ∘C [ [ M h ]∘[ M g ] ]₁ (id C {[ M f ]₀ x}))
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ' f (h ∘I g)) x ∘C (nat-η (μ' g h) ([ M f ]₀ x) ∘C [ M h ]₁ X)) (Functor.id (M g)) ⟩
        nat-η (μ' f (h ∘I g)) x ∘C (nat-η (μ' g h) ([ M f ]₀ x) ∘C [ M h ]₁ (id C {[ [ M g ]∘[ M f ] ]₀ x}))
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ' f (h ∘I g)) x ∘C (nat-η (μ' g h) ([ M f ]₀ x) ∘C X)) (Functor.id (M h)) ⟩
        nat-η (μ' f (h ∘I g)) x ∘C (nat-η (μ' g h) ([ M f ]₀ x) ∘C id C {[ [ M h ]∘[ [ M g ]∘[ M f ] ] ]₀ x})
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ' f (h ∘I g)) x ∘C X) (Category.left-id C) ⟩
        nat-η (μ' f (h ∘I g)) x ∘C nat-η (μ' g h) ([ M f ]₀ x) ∎h
    
    abstract
      left-id' : {i j : Obj I} {f : Hom I i j} {x : Obj C} 
               → nat-η (μ' (id I) f) x ∘C ([ [ P₁ ]₀ f ]₁ (nat-η (η' i) x))
               ≅ nat-η Id⟨ [ P₁ ]₀ f ⟩ x
      left-id' {i} {j} {f} {x} = hbegin
        nat-η (μ' (id I {i}) f) x ∘C [ M f ]₁ (nat-η (η' i) x)
          ≅⟨ ≡-to-≅ (cong (λ X → nat-η (μ' (id I {i}) f) x ∘C X) (sym $ Category.right-id C)) ⟩
        nat-η (μ' (id I {i}) f) x ∘C (id C {[ [ M f ]∘[ M (id I {i}) ] ]₀ x} ∘C [ M f ]₁ (nat-η (η' i) x))
          ≅⟨ nat-eq {α = μ' (id I {i}) f ∘ᵥCat (id₂ Cat ∘ₕCat η' i)} 
                    {β = Id⟨ M f ⟩}
                    (functor-eq refl hrefl) 
                    (functor-eq ( cong (λ X → Functor.F₀ (Functor.F₀ P₁ X)) (left-id I) ) 
                                $ het-implicit-fun-ext (het-fun-ext hrefl $ λ (a : Obj C) → hcong (λ X → {b : Obj C} → Hom C a b → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                  (≡-to-≅ (left-id I))) 
                                $ λ (a : Obj C) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (b : Obj C) → hcong (λ X → Hom C a b → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                                  (≡-to-≅ (left-id I))) 
                                $ λ (b : Obj C) → het-fun-ext (het-fun-ext hrefl $ λ (f : Hom C a b) → hcong (λ X → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                             (≡-to-≅ (left-id I))) 
                                $ λ (f : Hom C a b) → hcong (λ X → Functor.F₁ (Functor.F₀ P₁ X) f) (≡-to-≅ (left-id I)) )
                    laxFunId₁ 
                    x ⟩
        nat-η Id⟨ M f ⟩ x ∎h
    
    abstract
      right-id' : {i j : Obj I} {f : Hom I i j} {x : Obj C} 
                → nat-η (μ' f (id I)) x ∘C nat-η (η' j) ([ [ P₁ ]₀ f ]₀ x)
                ≅ nat-η Id⟨ [ P₁ ]₀ f ⟩ x
      right-id' {i} {j} {f} {x} = hbegin
        nat-η (μ' f (id I)) x ∘C nat-η (η' j) ([ [ P₁ ]₀ f ]₀ x)
          ≅⟨ ≡-to-≅ (cong (λ X → nat-η (μ' f (id I)) x ∘C X) (sym (Category.left-id C))) ⟩
        nat-η (μ' f (id I)) x ∘C (nat-η (η' j) ([ M f ]₀ x) ∘C id C {[ M f ]₀ x}) 
          ≅⟨ nat-eq {α = μ' f (id I) ∘ᵥCat (η' j ∘ₕCat id₂ Cat')}
                    {β = Id⟨ [ P₁ ]₀ f ⟩}
                    (functor-eq refl hrefl)
                    (functor-eq ( cong (λ X → Functor.F₀ (Functor.F₀ P₁ X)) (right-id I) ) 
                                $ het-implicit-fun-ext (het-fun-ext hrefl $ λ (a : Obj C) → hcong (λ X → {b : Obj C} → Hom C a b → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                  (≡-to-≅ (right-id I))) 
                                $ λ (a : Obj C) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (b : Obj C) → hcong (λ X → Hom C a b → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                                  (≡-to-≅ (right-id I))) 
                                $ λ (b : Obj C) → het-fun-ext (het-fun-ext hrefl $ λ (f : Hom C a b) → hcong (λ X → Hom C (Functor.F₀ (Functor.F₀ P₁ X) a) (Functor.F₀ (Functor.F₀ P₁ X) b)) 
                                                                                                             (≡-to-≅ (right-id I))) 
                                $ λ (f : Hom C a b) → hcong (λ X → Functor.F₁ (Functor.F₀ P₁ X) f) (≡-to-≅ (right-id I)) ) 
                    laxFunId₂
                    x ⟩
        nat-η Id⟨ [ P₁ ]₀ f ⟩ x ∎h
