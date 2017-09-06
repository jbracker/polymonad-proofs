
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
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
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Monad.Atkey
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.CodiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.Definition

open Category
open NaturalTransformation
open StrictTwoCategory

module Theory.TwoFunctor.Properties.FromAtkeyParameterizedMonad where

AtkeyParameterizedMonad→LaxTwoFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : AtkeyParameterizedMonad C S) 
  → LaxTwoFunctor (codiscreteHomCatTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})
AtkeyParameterizedMonad→LaxTwoFunctor {C = C} {S} F = record
  { P₀ = λ _ → C
  ; P₁ = P
  ; η = λ {x} → η' x
  ; μ = λ {x} {y} {z} {f} {g} → μ' x y z f g
  ; laxFunId₁ = λ {x} {y} {f} → laxFunId₁ x y f
  ; laxFunId₂ = λ {x} {y} {f} → laxFunId₂ x y f
  ; laxFunAssoc = λ {w} {x} {y} {z} {f} {g} {h} → laxFunAssoc w x y z f g h
  ; μ-natural₁ = λ {a b c} f {x y} {_} → μ-natural₁ {a} {b} {c} f {x} {y}
  ; μ-natural₂ = λ {a b c} g {x y} {_} → μ-natural₂ {a} {b} {c} g {x} {y}
  } where
    T = AtkeyParameterizedMonad.T F
    
    _∘C_ = Category._∘_ C
    _∘S_ = Category._∘_ S
    
    ApplyT : {x y : Obj S} → Hom S x y → Functor C C
    ApplyT {x} {y} _ = functor 
      (λ (c : Obj C) → Functor.F₀ T (y , x , c)) 
      (λ {a : Obj C} {b : Obj C} (g : Hom C a b) → Functor.F₁ T (id S {y} , id S {x} , g))
      (λ {a : Obj C} → Functor.id T)
      (λ {a : Obj C} {b : Obj C} {c : Obj C} {g} {h} → trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (h ∘C g))) (sym (left-id S {y})) (sym (left-id S {x})))
                                                             (Functor.compose T {y , x , a} {y , x , b} {y , x , c} {id S {y} , id S {x} , g} {id S {y} , id S {x} , h}))
  
    stateHomIndep : {x y : Obj S} → (fS : Hom S x y) (gS : Hom S x y)
                  → NaturalTransformation (ApplyT fS) (ApplyT gS)
    stateHomIndep fS gS = naturalTransformation 
      (λ (x : Obj C) → id C {[ ApplyT fS ]₀ x}) 
      (λ {a : Obj C} {b : Obj C} {f : Hom C a b} → trans (left-id C {f = [ ApplyT fS ]₁ f}) (sym (right-id C {f = [ ApplyT fS ]₁ f})))
    
    P : {x y : Obj S} 
      → Functor (HomCat (codiscreteHomCatTwoCategory S) x y) (HomCat functorTwoCategory C C)
    P {x} {y} = functor 
       (λ (fS : Hom S x y) → ApplyT fS) 
       (λ {fS : Hom S x y} {gS : Hom S x y} (f : Lift ⊤) → stateHomIndep fS gS)
       (λ {fS : Hom S x y} → refl)
       (λ {fS : Hom S x y} {gS : Hom S x y} {hS : Hom S x y} {f : Lift ⊤} {g : Lift ⊤} → natural-transformation-eq (fun-ext (λ x → sym (right-id C))))
    
    η' : (s : Obj S) → NaturalTransformation Id[ C ] (ApplyT (id S {s}))
    η' s = naturalTransformation
             (η (AtkeyParameterizedMonad.NatTrans-η F s))
             (λ {a : Obj C} {b : Obj C} {f : Hom C a b} → natural (AtkeyParameterizedMonad.NatTrans-η F s) {a} {b} {f})

    μ' : (x y z : Obj S)
       → (f : Hom S x y)
       → (g : Hom S y z)
       → NaturalTransformation ([ ApplyT g ]∘[ ApplyT f ]) (ApplyT (g ∘S f))
    μ' x y z f g = naturalTransformation
                   (η (AtkeyParameterizedMonad.NatTrans-μ F z y x))
                   (λ {a : Obj C} {b : Obj C} {f : Hom C a b} → natural (AtkeyParameterizedMonad.NatTrans-μ F z y x) {a} {b} {f})
    
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      μ-natural₁ : {i j k : Obj S} → (f : Hom S i j) → {x y : Hom S j k}
                 → ⟨ stateHomIndep (x ∘S f) (y ∘S f) ⟩∘ᵥ⟨ μ' i j k f x ⟩
                 ≡ ⟨ μ' i j k f y ⟩∘ᵥ⟨ ⟨ stateHomIndep x y ⟩∘ₕ⟨ stateHomIndep f f ⟩ ⟩
      μ-natural₁ {i} {j} {k} f {x} {y} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        id C {[ ApplyT (y ∘S f) ]₀ c} ∘C nat-η (μ' i j k f x) c
          ≡⟨ right-id C ⟩ 
        nat-η (μ' i j k f x) c
          ≡⟨ sym (left-id C) ⟩ 
        nat-η (μ' i j k f y) c ∘C id C
          ≡⟨ cong (λ X → nat-η (μ' i j k f y) c ∘C X) (sym (Functor.id (ApplyT x))) ⟩ 
        nat-η (μ' i j k f y) c ∘C [ ApplyT x ]₁ (id C)
          ≡⟨ cong (λ X → nat-η (μ' i j k f y) c ∘C X) (sym (right-id C)) ⟩ 
        nat-η (μ' i j k f y) c ∘C (id C ∘C [ ApplyT x ]₁ (id C)) ∎

    abstract
      μ-natural₂ : {a b c : Obj S} → (g : Hom S b c) → {x y : Hom S a b}
                 → ⟨ stateHomIndep (g ∘S x) (g ∘S y) ⟩∘ᵥ⟨ μ' a b c x g ⟩
                 ≡ ⟨ μ' a b c y g ⟩∘ᵥ⟨ ⟨ stateHomIndep g g ⟩∘ₕ⟨ stateHomIndep x y ⟩ ⟩
      μ-natural₂ {i} {j} {k} g {x} {y} = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
        id C ∘C nat-η (μ' i j k x g) c 
          ≡⟨ right-id C ⟩
        nat-η (μ' i j k x g) c 
          ≡⟨ sym (left-id C) ⟩
        nat-η (μ' i j k y g) c ∘C id C
          ≡⟨ cong (λ X → nat-η (μ' i j k y g) c ∘C X) (sym (Functor.id (ApplyT g))) ⟩
        nat-η (μ' i j k y g) c ∘C [ ApplyT g ]₁ (id C)
          ≡⟨ cong (λ X → nat-η (μ' i j k y g) c ∘C X) (sym (right-id C)) ⟩
        nat-η (μ' i j k y g) c ∘C (id C ∘C [ ApplyT g ]₁ (id C)) ∎
    
    abstract
      laxFunId₁ : (x y : Obj S) (f : Hom S x y)
                → ⟨ μ' x x y (id S) f ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT f ⟩ ⟩∘ₕ⟨ (η' x) ⟩ ⟩
                ≅ id₂ functorTwoCategory
      laxFunId₁ x y f = het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext (het-fun-ext hrefl (λ x → hrefl)) $ λ (c : Obj C) → hbegin
        η ⟨ μ' x x y (id S) f ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT f ⟩ ⟩∘ₕ⟨ (η' x) ⟩ ⟩ c
          ≅⟨ hrefl ⟩
        η (μ' x x y (id S) f) c ∘C (id C ∘C [ ApplyT f ]₁ (η (η' x) c))
          ≅⟨ hcong (λ X → η (μ' x x y (id S) f) c ∘C X) (≡-to-≅ $ right-id C) ⟩
        η (μ' x x y (id S) f) c ∘C [ ApplyT f ]₁ (η (η' x) c)
          ≅⟨ ≡-to-≅ $ AtkeyParameterizedMonad.left-id F ⟩
        id C {[ ApplyT f ]₀ c} ∎h
    
    abstract
      laxFunId₂ : (x y : Obj S) (f : Hom S x y)
                → ⟨ μ' x y y f (id S) ⟩∘ᵥ⟨ ⟨ η' y ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩
                ≅ id₂ functorTwoCategory
      laxFunId₂ x y f = het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext hrefl $ λ (c : Obj C) → hbegin
        η ⟨ μ' x y y f (id S) ⟩∘ᵥ⟨ ⟨ η' y ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩ c
          ≅⟨ hrefl ⟩
        η (μ' x y y f (id S)) c ∘C (η (η' y) ([ ApplyT f ]₀ c) ∘C id C)
          ≅⟨ hcong (λ X → η (μ' x y y f (id S)) c ∘C X) (≡-to-≅ $ left-id C) ⟩
        η (μ' x y y f (id S)) c ∘C η (η' y) ([ ApplyT f ]₀ c)
          ≅⟨ ≡-to-≅ $ AtkeyParameterizedMonad.right-id F ⟩
        id C {[ ApplyT (id S ∘S f) ]₀ c} ∎h
        where
          abstract
            helper : (c : Obj C)
                   → (q : ApplyT f ≡ ApplyT (id S {y} ∘S f))
                   → η Id⟨ ApplyT (id S ∘S f) ⟩ c
                   ≡ η (subst₂ NaturalTransformation q refl Id⟨ ApplyT f ⟩) c
            helper c refl = refl
    
    abstract
      laxFunAssoc : (w x y z : Obj S) (f : Hom S w x) (g : Hom S x y) (h : Hom S y z)
                  → ⟨ μ' w y z (g ∘S f) h ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT h ⟩ ⟩∘ₕ⟨ μ' w x y f g ⟩ ⟩
                  ≅ ⟨ μ' w x z f (h ∘S g) ⟩∘ᵥ⟨ ⟨ μ' x y z g h ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩
      laxFunAssoc w x y z f g h = het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext hrefl $ λ (c : Obj C) → hbegin
        η ⟨ μ' w y z (g ∘S f) h ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT h ⟩ ⟩∘ₕ⟨ μ' w x y f g ⟩ ⟩ c
          ≅⟨ hrefl ⟩
        η (μ' w y z (g ∘S f) h) c ∘C (id C {[ ApplyT h ]₀ ([ ApplyT (g ∘S f) ]₀ c)} ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c))
          ≅⟨ hcong (λ X → η (μ' w y z (g ∘S f) h) c ∘C X) (≡-to-≅ $ right-id C) ⟩
        η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)
          ≅⟨ ≡-to-≅ $ sym (left-id C) ⟩
        (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C id C {[ [ [ [ P ]₀ h ]∘[ [ P ]₀ g ] ]∘[ [ P ]₀ f ] ]₀ c}
          ≅⟨ hrefl ⟩
        (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C id C {[ ApplyT h ]₀ ([ ApplyT g ]₀ ([ ApplyT f ]₀ c))}
          ≅⟨ hcong (λ X → (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C X) (hsym (≡-to-≅ (Functor.id (ApplyT h)))) ⟩
        (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C [ ApplyT h ]₁ (id C {[ ApplyT g ]₀ ([ ApplyT f ]₀ c)})
          ≅⟨ hcong (λ X → (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C [ ApplyT h ]₁ X) (hsym (≡-to-≅ (Functor.id (ApplyT g)))) ⟩
        (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c})
          ≅⟨ hcong (λ X → X ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}) ) (≡-to-≅ $ AtkeyParameterizedMonad.assoc F) ⟩
        (η (μ' w x z f (h ∘S g)) c ∘C η (μ' x y z g h) ([ ApplyT f ]₀ c)) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c})
          ≅⟨ ≡-to-≅ $ sym (assoc C) ⟩
        η (μ' w x z f (h ∘S g)) c ∘C (η (μ' x y z g h) ([ ApplyT f ]₀ c) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}))
          ≅⟨ hrefl ⟩
        η ⟨ μ' w x z f (h ∘S g) ⟩∘ᵥ⟨ ⟨ μ' x y z g h ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩ c ∎h
