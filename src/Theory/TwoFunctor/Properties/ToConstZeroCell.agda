
open import Level
open import Function hiding ( _∘_ ; id )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; subst₂ to hsubst₂ )

open import Substitution

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.Definition

module Theory.TwoFunctor.Properties.ToConstZeroCell where

open StrictTwoCategory
open LaxTwoFunctor

LaxTwoFunctor→ConstLaxTwoFunctor : {ℓC₀ ℓC₁ ℓC₂ ℓD₀ ℓD₁ ℓD₂ : Level}
                                 → {C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}}
                                 → {D : StrictTwoCategory {ℓD₀} {ℓD₁} {ℓD₂}}
                                 → {constD : Cell₀ D}
                                 → (F : LaxTwoFunctor C D)
                                 → ((c : Cell₀ C) → P₀ F c ≡ constD)
                                 → ConstLaxTwoFunctor C D constD
LaxTwoFunctor→ConstLaxTwoFunctor {ℓC₀} {ℓC₁} {ℓC₂} {ℓD₀} {ℓD₁} {ℓD₂} {C} {D} {constD} F constF
  = const-lax-two-functor constP₁ constη {!!} {!!} {!!} {!!} {!!} {!!}
  where
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    
    constP₁ : {x y : Cell₀ C} → Functor (HomCat C x y) (HomCat D constD constD)
    constP₁ {x} {y} = subst₂ (λ X Y → Functor (HomCat C x y) (HomCat D X Y)) (constF x) (constF y) (P₁ F)
    
    subst₂≅id : {Aℓ Bℓ Pℓ : Level} {A : Set Aℓ} {B : Set Bℓ}
              → (P : A → B → Set Pℓ)
              → {x₁ x₂ : A} {y₁ y₂ : B}
              → (eq₁ : x₁ ≡ x₂) → (eq₂ : y₁ ≡ y₂)
              → (x : P x₁ y₁)
              → subst₂ P eq₁ eq₂ x ≅ x
    subst₂≅id P refl refl x = hrefl
    
    constP₁-eq : {x y : Cell₀ C} → constP₁ {x} {y} ≅ P₁ F {x} {y}
    constP₁-eq {x} {y} = subst₂≅id (λ X Y → Functor (HomCat C x y) (HomCat D X Y)) (constF x) (constF y) (P₁ F) 

    η' : {x : Cell₀ C} → Cell₂ D (id₁ D {P₀ F x}) ([ P₁ F {x} {x} ]₀ (id₁ C {x}))
    η' {x} = η F {x}
    
    constη : {x : Cell₀ C} → Cell₂ D (id₁ D {constD}) ([ constP₁ {x} {x} ]₀ (id₁ C {x}))
    constη {x} = het-subst₂-dep (λ X Y → Cell₂ D (id₁ D {X}) ([ Y ]₀ (id₁ C {x}))) (constF x) (hsym $ constP₁-eq {x} {x}) (η F {x})

    constμ-subst : {x y z : Cell₀ C}
                 → {f : Cell₁ C x y} {g : Cell₁ C y z}
                 → {Px Py Pz : Cell₀ D}
                 → {X₁ : Functor (HomCat C y z) (HomCat D Py Pz)}
                 → {Y₁ : Functor (HomCat C x y) (HomCat D Px Py)}
                 → {Z₁ : Functor (HomCat C x z) (HomCat D Px Pz)}
                 → {X₂ : Functor (HomCat C y z) (HomCat D constD constD)}
                 → {Y₂ : Functor (HomCat C x y) (HomCat D constD constD)}
                 → {Z₂ : Functor (HomCat C x z) (HomCat D constD constD)}
                 → Px ≡ constD → Py ≡ constD → Pz ≡ constD
                 → X₁ ≅ X₂ → Y₁ ≅ Y₂ → Z₁ ≅ Z₂
                 → Cell₂ D ([ X₁ ]₀ g ∘D [ Y₁ ]₀ f) ([ Z₁ ]₀ (g ∘C f))
                 → Cell₂ D ([ X₂ ]₀ g ∘D [ Y₂ ]₀ f) ([ Z₂ ]₀ (g ∘C f))
    constμ-subst {x} {y} {z} refl refl refl hrefl hrefl hrefl morph = morph
    
    constμ : {x y z : Cell₀ C} {f : Cell₁ C x y} {g : Cell₁ C y z}
           → Cell₂ D ([ constP₁ {y} {z} ]₀ g ∘D [ constP₁ {x} {y} ]₀ f) ([ constP₁ {x} {z} ]₀ (g ∘C f))
    constμ {x} {y} {z} {f} {g} = constμ-subst {x} {y} {z} {f} {g} (constF x) (constF y) (constF z) {!!} {!!} {!!} (μ F {x} {y} {z} {f} {g}) 
