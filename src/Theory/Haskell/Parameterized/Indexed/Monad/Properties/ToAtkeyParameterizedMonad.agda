
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong )
open ≡-Reasoning

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToAtkeyParameterizedMonad
  {ℓC₀ ℓC₁ ℓI : Level}
  {C : Category {ℓC₀} {ℓC₁}} {I : Set ℓI}
  where

open Category
open Triple renaming ( proj₁ to p₁ ; proj₂ to p₂ ; proj₃ to p₃ )

private
  _∘C_ = _∘_ C

IndexedMonad→AtkeyParameterizedMonad 
  : (Σ ({i j : I} → Hom (Codisc I) i j → Functor C C) (IndexedMonad (Codisc I))) 
  → AtkeyParameterizedMonad C (Disc I)
IndexedMonad→AtkeyParameterizedMonad (T , IxMonad) =
  atkey-parameterized-monad F η μ
    (λ {i} {a b} {f} → naturalη {i} {a} {b} {f})
    (λ {x} {i j} {f} → dinaturalη {x} {i} {j} {f})
    (λ {i j k} {a b} {f} → naturalμ {i} {j} {k} {a} {b} {f})
    (λ {i j} {x} {k l} {f} → naturalμ₁ {i} {j} {x} {k} {l} {f})
    (λ {i j} {x} {k l} {f} → naturalμ₂ {i} {j} {x} {k} {l} {f})
    (λ {i j} {x} {k l} {f} → dinaturalμ {i} {j} {x} {k} {l} {f})
    (λ {x} {i j k l} → assoc' {x} {i} {j} {k} {l})
    (λ {x} {i j} → left-id' {x} {i} {j})
    (λ {x} {i j} → right-id' {x} {i} {j})
  where
    open NaturalTransformation renaming ( η to nat-η )
    open IndexedMonad IxMonad renaming ( functor to ix-functor ; η to ix-η ; μ to ix-μ )
    
    F : Functor ((Disc I) op ×C Disc I ×C C) C
    F = functor F₀ F₁ F-id (λ {a b c} {f} {g} → F-compose {a} {b} {c} {f} {g})
      where
        F₀ : Obj ((Disc I op) ×C Disc I ×C C) → Obj C
        F₀ (i ,' j ,' a) = Functor.F₀ (T (codisc j i)) a
        
        F₁ : {a b : Obj ((Disc I op) ×C Disc I ×C C)} → Hom ((Disc I op) ×C Disc I ×C C) a b → Hom C (F₀ a) (F₀ b)
        F₁ {i ,' j ,' a} {.i ,' .j ,' b} (refl ,' refl ,' f) = Functor.F₁ (T (codisc j i)) f
        
        F-id : {a : Obj ((Disc I op) ×C Disc I ×C C)} → Functor.F₁ (T (codisc (p₁ a) (p₂ a))) (id C {p₃ a}) ≡ id C
        F-id {i ,' j ,' a} = Functor.id (T (codisc i j))
        
        F-compose : {a b c : Obj ((Disc I op) ×C Disc I ×C C)}
                  → {f : Hom ((Disc I op) ×C Disc I ×C C) a b} {g : Hom ((Disc I op) ×C Disc I ×C C) b c} 
                  → F₁ ((((Disc I op) ×C Disc I ×C C) ∘ g) f) ≡ (C ∘ F₁ g) (F₁ f)
        F-compose {i ,' j ,' a} {.i ,' .j ,' b} {.i ,' .j ,' c} {refl ,' refl ,' f} {refl ,' refl ,' g} = Functor.compose (T (codisc j i))
    
    η : {a : Obj C} {s : Obj (Disc I)} → Hom C a ([ F ]₀ (s ,' s ,' a))
    η {a} {i} = nat-η (ix-η i) a
    
    μ : {a : Obj C} {s₁ s₂ s₃ : Obj (Disc I)} → Hom C ([ F ]₀ (s₁ ,' s₂ ,' [ F ]₀ (s₂ ,' s₃ ,' a))) ([ F ]₀ (s₁ ,' s₃ ,' a))
    μ {a} {i} {j} {k} = nat-η (ix-μ (codisc k j) (codisc j i)) a

    naturalη : {s : Obj (Disc I)} {a b : Obj C} {f : Hom C a b}
             → [ F ]₁ (id (Disc I op) {s} ,' id (Disc I) {s} ,' f) ∘C η ≡ η ∘C f
    naturalη {i} {a} {b} {f} = natural (ix-η i) {a} {b} {f}

    dinaturalη : {x : Obj C} {i j : Obj (Disc I)} {f : Hom (Disc I) i j}
               → [ F ]₁ (id (Disc I) ,' f ,' id C {x}) ∘C η {x} ≡ [ F ]₁ (f ,' id (Disc I) ,' id C) ∘C η {x}
    dinaturalη {x} {i} {.i} {refl} = refl

    naturalμ : {s₁ s₂ s₃ : Obj (Disc I)} {a b : Obj C} {f : Hom C a b}
             → [ F ]₁ (id (Disc I op) {s₁} ,' id (Disc I) {s₃} ,' f) ∘C μ {a} {s₁} {s₂} {s₃}
             ≡ μ {b} {s₁} {s₂} {s₃} ∘C ([ F ]₁ (id (Disc I op) ,' id (Disc I) ,' [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' f)))
    naturalμ {i} {j} {k} {a} {b} {f} = natural (ix-μ (codisc k j) (codisc j i)) {a} {b} {f}

    naturalμ₁ : {s₂ s₃ : Obj (Disc I)} {x : Obj C} {a b : Obj (Disc I op)} {f : Hom (Disc I op) a b}
              → [ F ]₁ (f ,' id (Disc I) ,' id C) ∘C (μ {x} {a} {s₂} {s₃})
              ≡ μ {x} {b} {s₂} {s₃} ∘C [ F ]₁ (f ,' id (Disc I) ,' [ F ]₁ (id (Disc I) ,' id (Disc I) ,' id C))
    naturalμ₁ {s₂} {s₃} {x} {a} {.a} {refl} = begin
      [ F ]₁ (refl ,' id (Disc I) ,' id C) ∘C (μ {x} {a} {s₂} {s₃})
        ≡⟨ cong (λ X → X ∘C μ) (Functor.id F) ⟩
      id C ∘C (μ {x} {a} {s₂} {s₃})
        ≡⟨ Category.right-id C ⟩
      μ {x} {a} {s₂} {s₃}
        ≡⟨ sym $ Category.left-id C ⟩
      μ {x} {a} {s₂} {s₃} ∘C id C
        ≡⟨ cong (λ X → μ ∘C X) (sym $ Functor.id F) ⟩
      μ {x} {a} {s₂} {s₃} ∘C [ F ]₁ (refl ,' id (Disc I) ,' id C)
        ≡⟨ cong (λ X → μ ∘C [ F ]₁ (refl ,' id (Disc I) ,' X)) (sym $ Functor.id F) ⟩
      μ {x} {a} {s₂} {s₃} ∘C [ F ]₁ (refl ,' id (Disc I) ,' [ F ]₁ (id (Disc I) ,' id (Disc I) ,' id C)) ∎

    naturalμ₂ : {s₁ s₂ : Obj (Disc I)} {x : Obj C} {a b : Obj (Disc I)} {f : Hom (Disc I) a b}
              → [ F ]₁ (id (Disc I op) ,' f ,' id C) ∘C (μ {x} {s₁} {s₂} {a})
              ≡ μ {x} {s₁} {s₂} {b} ∘C [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' [ F ]₁ (id (Disc I) ,' f ,' id C))
    naturalμ₂ {s₁} {s₂} {x} {a} {.a} {refl} = begin
      ([ F ]₁ (id (Disc I op) ,' refl ,' id C) ∘C μ)
        ≡⟨ cong (λ X → X ∘C μ) (Functor.id F) ⟩
      id C ∘C μ
        ≡⟨ Category.right-id C ⟩
      μ
        ≡⟨ sym (Category.left-id C) ⟩
      μ ∘C id C
        ≡⟨ cong (λ X → μ ∘C X) (sym (Functor.id F)) ⟩
      μ ∘C [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' id C)
        ≡⟨ cong (λ X → μ ∘C [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' X)) (sym (Functor.id F)) ⟩
      μ ∘C [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' [ F ]₁ (id (Disc I) ,' refl ,' id C)) ∎

    dinaturalμ : {s₁ s₃ : Obj (Disc I)} {x : Obj C} {a b : Obj (Disc I)} {f : Hom (Disc I) a b}
               → μ {x} {s₁} {a} {s₃} ∘C [ F ]₁ (id (Disc I op) ,' id (Disc I) ,' [ F ]₁ (f ,' id (Disc I) ,' id C))
               ≡ μ {x} {s₁} {b} {s₃} ∘C [ F ]₁ (id (Disc I op) ,' f ,' [ F ]₁ (id (Disc I) ,' id (Disc I) ,' id C))
    dinaturalμ {s₁} {s₃} {x} {a} {.a} {refl} = refl

    assoc' : {x : Obj C} {s₀ s₁ s₂ s₃ : Obj (Disc I)}
           → μ {x} {s₀} {s₁} {s₃} ∘C ([ F ]₁ (id (Disc I) ,' id (Disc I) ,' μ {x} {s₁} {s₂} {s₃})) ≡ μ ∘C μ
    assoc' = ≅-to-≡ $ μ-coher

    left-id' : {x : Obj C} {s₁ s₂ : Obj (Disc I)}
             → μ {x} {s₁} {s₂} {s₂} ∘C ([ F ]₁ (id (Disc I op) ,' id (Disc I) ,' η)) ≡ id C
    left-id' = ≅-to-≡ $ η-left-coher

    right-id' : {x : Obj C} {s₁ s₂ : Obj (Disc I)}
              → μ {x} {s₁} {s₁} {s₂} ∘C η ≡ id C
    right-id' = ≅-to-≡ $ η-right-coher
