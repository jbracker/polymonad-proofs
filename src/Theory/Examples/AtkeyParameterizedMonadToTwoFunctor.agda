
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
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Atkey
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor

open Category
open NaturalTransformation
open StrictTwoCategory

module Theory.Examples.AtkeyParameterizedMonadToTwoFunctor where

AtkeyFunctor→LaxTwoFunctor 
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}}
  → {S : Category {ℓS₀} {ℓS₁}}
  → {T : Functor (S op ×C S ×C C) C}
  → (F : AtkeyParameterizedMonad C S T) 
  → LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})
AtkeyFunctor→LaxTwoFunctor {C = C} {S} {T} F = record
  { P₀ = λ _ → C
  ; P₁ = P
  ; η = λ {x} → η' x
  ; μ = λ {x} {y} {z} {f} {g} → μ' x y z f g
  ; laxFunId₁ = λ {x} {y} {f} → laxFunId₁ x y f
  ; laxFunId₂ = λ {x} {y} {f} → laxFunId₂ x y f
  ; laxFunAssoc = {!!}
  } where
    
    _∘C_ = Category._∘_ C
    _∘S_ = Category._∘_ S
    
    ApplyT : {x y : Obj S} → Hom S x y → Functor C C
    ApplyT {x} {y} f = functor 
      (λ A → Functor.F₀ T (y , x , A)) 
      (λ f → Functor.F₁ T (id S {y} , id S {x} , f))
      (λ {a} → Functor.id T)
      (λ {a} {b} {c} {f} {g} → trans (cong₂ (λ X Y → Functor.F₁ T (X , Y , (g ∘C f))) (sym (left-id S)) (sym (left-id S))) (Functor.compose T))
  
    stateHomIndep : {x y : Obj S} → (fS : Hom S x y) (gS : Hom S x y)
                  → NaturalTransformation (ApplyT fS) (ApplyT gS)
    stateHomIndep fS gS = naturalTransformation 
      (λ x → id C {[ ApplyT fS ]₀ x}) 
      (λ {a} {b} {f} → trans (left-id C {f = [ ApplyT fS ]₁ f}) (sym (right-id C {f = [ ApplyT fS ]₁ f})))
    
    P : {x y : Cell₀ (Category→StrictTwoCategory S)} 
      → Functor (HomCat (Category→StrictTwoCategory S) x y) (HomCat functorTwoCategory C C)
    P = λ {x} {y} → functor 
       (λ fS → ApplyT fS) 
       (λ {fS} {gS} _ → stateHomIndep fS gS)
       (λ {fS} → refl)
       (λ {fS} {gS} {hS} {_} {_} → natural-transformation-eq (fun-ext (λ x → sym (right-id C))))

    η' : (s : Obj S) → NaturalTransformation Id[ C ] (ApplyT (id S {s}))
    η' s = naturalTransformation
             (η (AtkeyParameterizedMonad.NatTrans-η F s))
             (λ {a} {b} {f} → natural (AtkeyParameterizedMonad.NatTrans-η F s) {a} {b} {f})

    μ' : (x y z : Obj S)
       → (f : Hom S x y)
       → (g : Hom S y z)
       → NaturalTransformation ([ ApplyT g ]∘[ ApplyT f ]) (ApplyT (g ∘S f))
    μ' x y z f g = naturalTransformation
                   (η (AtkeyParameterizedMonad.NatTrans-μ F z y x))
                   (λ {a} {b} {f} → natural (AtkeyParameterizedMonad.NatTrans-μ F z y x) {a} {b} {f})

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
                                  {F₁ = λ a b h → Functor.F₁ (ApplyT f) {a} {b} h} {G₁ = λ a b h → Functor.F₁ (ApplyT (id S ∘S f)) {a} {b} h}
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
      
{-compNaturalTransformationHorz 
  : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓE₀ ℓE₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} {E : Category {ℓE₀} {ℓE₁}}
  → {G G' : Functor D E} {F F' : Functor C D}
  → NaturalTransformation G G' → NaturalTransformation F F'
  → NaturalTransformation [ G ]∘[ F ] [ G' ]∘[ F' ]
-}
-- compNaturalTransformationHorz {C = C} {D} {E} {G} {G'} {F} {F'} α β =  record 
--  η c = ηα ([ F' ]₀ c) ∘E [ G ]₁ (ηβ c)
