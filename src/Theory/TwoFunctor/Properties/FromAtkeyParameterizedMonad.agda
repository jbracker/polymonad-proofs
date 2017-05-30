
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
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

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
open import Theory.TwoCategory.Examples
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
    
    laxFunId₁ : (x y : Obj S) (f : Hom S x y)
              → ⟨ stateHomIndep f f ⟩∘ᵥ⟨ ⟨ μ' x x y (id S) f ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT f ⟩ ⟩∘ₕ⟨ (η' x) ⟩ ⟩ ⟩
              ≡ stateHomIndep f f
    laxFunId₁ x y f = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
      η ⟨ stateHomIndep f f ⟩∘ᵥ⟨ ⟨ μ' x x y (id S) f ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT f ⟩ ⟩∘ₕ⟨ (η' x) ⟩ ⟩ ⟩ c
        ≡⟨⟩
      id C {[ ApplyT f ]₀ c} ∘C (η (μ' x x y (id S) f) c ∘C (id C ∘C [ ApplyT f ]₁ (η (η' x) c)))
        ≡⟨ cong (λ X → id C {[ ApplyT f ]₀ c} ∘C (η (μ' x x y (id S) f) c ∘C X)) (right-id C) ⟩
      id C {[ ApplyT f ]₀ c} ∘C (η (μ' x x y (id S) f) c ∘C [ ApplyT f ]₁ (η (η' x) c))
        ≡⟨ cong (λ X → id C {[ ApplyT f ]₀ c} ∘C X) (AtkeyParameterizedMonad.left-id F) ⟩
      id C {[ ApplyT f ]₀ c} ∘C id C
        ≡⟨ left-id C ⟩
      id C {[ ApplyT f ]₀ c}
        ≡⟨⟩
      η (stateHomIndep f f) c ∎

    laxFunId₂ : (x y : Obj S) (f : Hom S x y)
              → ⟨ stateHomIndep (id S ∘S f) f ⟩∘ᵥ⟨ ⟨ μ' x y y f (id S) ⟩∘ᵥ⟨ ⟨ η' y ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩ ⟩
              ≡ ρ functorTwoCategory ([ P ]₀ f)
    laxFunId₂ x y f = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
      η ⟨ stateHomIndep (id S ∘S f) f ⟩∘ᵥ⟨ ⟨ μ' x y y f (id S) ⟩∘ᵥ⟨ ⟨ η' y ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩ ⟩ c
        ≡⟨⟩
      η (stateHomIndep (id S ∘S f) f) c ∘C (η (μ' x y y f (id S)) c ∘C (η (η' y) ([ ApplyT f ]₀ c) ∘C id C))
        ≡⟨ cong (λ X → η (stateHomIndep (id S ∘S f) f) c ∘C (η (μ' x y y f (id S)) c ∘C X)) (left-id C) ⟩
      η (stateHomIndep (id S ∘S f) f) c ∘C (η (μ' x y y f (id S)) c ∘C η (η' y) ([ ApplyT f ]₀ c))
        ≡⟨ cong (λ X → η (stateHomIndep (id S ∘S f) f) c ∘C X) (AtkeyParameterizedMonad.right-id F) ⟩
      η (stateHomIndep (id S ∘S f) f) c ∘C id C
        ≡⟨ left-id C ⟩
      η (stateHomIndep (id S ∘S f) f) c
        ≡⟨⟩
      id C {[ ApplyT (id S ∘S f) ]₀ c}
        ≡⟨⟩
      η Id⟨ ApplyT (id S ∘S f) ⟩ c
        ≡⟨ helper c (sym $ functor-eq refl hrefl) ⟩
      η (subst₂ NaturalTransformation
                (sym $ functor-eq {idF = λ {a} → Functor.id T {y , x , a}}
                                  {composeF = λ {a} {b} {c} {h} {k} → Functor.compose (ApplyT (id S ∘S f)) {a} {b} {c} {h} {k}}
                                  refl hrefl)
                refl Id⟨ ApplyT f ⟩) c
        ≡⟨ cong (λ X → η (subst₂ NaturalTransformation (sym $ functor-eq {idF = λ {a} → X {a}}
                                                                         {composeF = λ {a} {b} {c} {h} {k} → Functor.compose (ApplyT (id S ∘S f)) {a} {b} {c} {h} {k}}
                                                                         refl hrefl)
                                                        refl Id⟨ ApplyT f ⟩) c)
                         (implicit-fun-ext (λ a → proof-irrelevance (Functor.id T) (trans (cong (Functor.F₁ Id[ C ]) (Functor.id T)) (Functor.id Id[ C ])))) ⟩
        η (subst₂ NaturalTransformation
                (sym $ functor-eq {F₀ = [ ApplyT f ]₀} {G₀ = [ ApplyT (id S ∘S f) ]₀}
                                  {F₁ = λ {a} {b} h → Functor.F₁ (ApplyT f) {a} {b} h} {G₁ = λ {a} {b} h → Functor.F₁ (ApplyT (id S ∘S f)) {a} {b} h}
                                  {idF = trans (cong (Functor.F₁ Id[ C ]) (Functor.id T)) (Functor.id Id[ C ])}
                                  {composeF = λ {a} {b} {c} {h} {k} → Functor.compose (ApplyT (id S ∘S f)) {a} {b} {c} {h} {k}}
                                  refl hrefl)
                refl Id⟨ ApplyT f ⟩) c
        ≡⟨ cong (λ X → η (subst₂ NaturalTransformation (sym $ functor-eq {idF = trans (cong (Functor.F₁ Id[ C ]) (Functor.id T)) (Functor.id Id[ C ])}
                                                                         {composeF = λ {a} {b} {c} {h} {k} → X {a} {b} {c} {h} {k}} refl hrefl) refl Id⟨ ApplyT f ⟩) c)
                (implicit-fun-ext (λ a → implicit-fun-ext (λ b → implicit-fun-ext (λ c → implicit-fun-ext (λ h → implicit-fun-ext (λ k →
                  proof-irrelevance (Functor.compose (ApplyT (id S ∘S f)) {a} {b} {c} {h} {k})
                                    (trans (cong (Functor.F₁ Id[ C ]) (trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (k ∘C h))) (sym $ left-id S) (sym $ left-id S))
                                                                             (Functor.compose T)))
                                           (Functor.compose Id[ C ]))
                )))))) ⟩
      η (subst₂ NaturalTransformation
                (sym $ functor-eq {idF = trans (cong (Functor.F₁ Id[ C ]) (Functor.id T)) (Functor.id Id[ C ])}
                                  {composeF = λ {a} {b} {c} {h} {k} → trans (cong (Functor.F₁ Id[ C ])
                                                                                  (trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (k ∘C h))) (sym $ left-id S) (sym $ left-id S))
                                                                                         (Functor.compose T)))
                                                                            (Functor.compose Id[ C ])}
                                  refl hrefl)
                refl Id⟨ ApplyT f ⟩) c
        ≡⟨⟩
      η (ρ functorTwoCategory (ApplyT f)) c ∎
      where
        helper : (c : Obj C)
               → (q : ApplyT f ≡ ApplyT (id S {y} ∘S f))
               → η Id⟨ ApplyT (id S ∘S f) ⟩ c
               ≡ η (subst₂ NaturalTransformation q refl Id⟨ ApplyT f ⟩) c
        helper c refl = refl

    laxFunAssoc : (w x y z : Obj S) (f : Hom S w x) (g : Hom S x y) (h : Hom S y z)
                → ⟨ Functor.F₁ P {a = h ∘S (g ∘S f)} {b = (h ∘S g) ∘S f} (α (codiscreteHomCatTwoCategory S) f g h)
                  ⟩∘ᵥ⟨
                  ⟨ μ' w y z (g ∘S f) h ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT h ⟩ ⟩∘ₕ⟨ μ' w x y f g ⟩ ⟩ ⟩
                ≡ ⟨ μ' w x z f (h ∘S g) ⟩∘ᵥ⟨
                  ⟨ ⟨ μ' x y z g h ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩∘ᵥ⟨ α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h) ⟩ ⟩
    laxFunAssoc w x y z f g h = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin
      η ⟨ Functor.F₁ P {a = h ∘S (g ∘S f)} {b = (h ∘S g) ∘S f} (α (codiscreteHomCatTwoCategory S) f g h) ⟩∘ᵥ⟨ ⟨ μ' w y z (g ∘S f) h ⟩∘ᵥ⟨ ⟨ Id⟨ ApplyT h ⟩ ⟩∘ₕ⟨ μ' w x y f g ⟩ ⟩ ⟩ c
        ≡⟨⟩
      η (Functor.F₁ P {a = h ∘S (g ∘S f)} {b = (h ∘S g) ∘S f} (α (codiscreteHomCatTwoCategory S) f g h)) c ∘C
                    (  η (μ' w y z (g ∘S f) h) c
                    ∘C (id C {[ ApplyT h ]₀ ([ ApplyT (g ∘S f) ]₀ c)} ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) )
        ≡⟨ cong (λ X → η (Functor.F₁ P {a = h ∘S (g ∘S f)} {b = (h ∘S g) ∘S f} (α (codiscreteHomCatTwoCategory S) f g h)) c ∘C (η (μ' w y z (g ∘S f) h) c ∘C X )) (right-id C) ⟩
      η (Functor.F₁ P {a = h ∘S (g ∘S f)} {b = (h ∘S g) ∘S f} (α (codiscreteHomCatTwoCategory S) f g h)) c ∘C (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c) )
        ≡⟨ refl ⟩
      id C {[ ApplyT (h ∘S (g ∘S f)) ]₀ c} ∘C (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c) )
        ≡⟨ right-id C ⟩
      η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)
        ≡⟨ sym (left-id C) ⟩
      (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C id C {[ [ [ [ P ]₀ h ]∘[ [ P ]₀ g ] ]∘[ [ P ]₀ f ] ]₀ c}
        ≡⟨ refl ⟩
      (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C (η (functorAssociator ([ P ]₀ h) ([ P ]₀ g) ([ P ]₀ f)) c)
        ≡⟨ cong (λ X → (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C (η X c)) (sym (associator-eq ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h))) ⟩
      (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)
        ≡⟨ cong (λ X → X ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)) (sym (left-id C)) ⟩
      (  (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C id C {[ [ ApplyT h ]∘[ ApplyT g ] ]₀ ([ ApplyT f ]₀ c)} )
      ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)
        ≡⟨ cong (λ X → ((η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C X ) ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c))
                (sym $ Functor.id [ ApplyT h ]∘[ ApplyT g ]) ⟩
      (  (η (μ' w y z (g ∘S f) h) c ∘C [ ApplyT h ]₁ (η (μ' w x y f g) c)) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}) )
      ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)
        ≡⟨ cong (λ X →  (X ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}) ) ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)) (AtkeyParameterizedMonad.assoc F) ⟩
      (  (η (μ' w x z f (h ∘S g)) c ∘C η (μ' x y z g h) ([ ApplyT f ]₀ c)) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}) )
      ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)
        ≡⟨ cong (λ X → X ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c)) (sym (assoc C)) ⟩
      (  η (μ' w x z f (h ∘S g)) c ∘C (η (μ' x y z g h) ([ ApplyT f ]₀ c) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c})) )
      ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c) 
        ≡⟨ sym (assoc C) ⟩
      η (μ' w x z f (h ∘S g)) c ∘C (  (η (μ' x y z g h) ([ ApplyT f ]₀ c) ∘C [ [ ApplyT h ]∘[ ApplyT g ] ]₁ (id C {[ ApplyT f ]₀ c}))
                                   ∘C (η (α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h)) c) )
        ≡⟨⟩
      η ⟨ μ' w x z f (h ∘S g) ⟩∘ᵥ⟨ ⟨ ⟨ μ' x y z g h ⟩∘ₕ⟨ Id⟨ ApplyT f ⟩ ⟩ ⟩∘ᵥ⟨ α functorTwoCategory ([ P ]₀ f) ([ P ]₀ g) ([ P ]₀ h) ⟩ ⟩ c ∎
