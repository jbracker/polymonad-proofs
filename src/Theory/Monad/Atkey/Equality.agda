
open import Level
open import Function renaming ( id to idF )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; proof-irrelevance to het-proof-irrelevance )
open ≡-Reasoning 

open import Congruence
open import Extensionality

open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Monad.Atkey

module Theory.Monad.Atkey.Equality {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {S : Category {ℓS₀} {ℓS₁}} where

open Category
private
  _∘C_ = Category._∘_ C
  _∘S_ = Category._∘_ S

atkey-parameterized-monad-eq 
  : {T₀ : Functor (S op ×C S ×C C) C}
  → {T₁ : Functor (S op ×C S ×C C) C}
  → {η₀ : {a : Obj C} {s : Obj S} → Hom C a ([ T₀ ]₀ (s , s , a))}
  → {η₁ : {a : Obj C} {s : Obj S} → Hom C a ([ T₁ ]₀ (s , s , a))}
  → {μ₀ : {a : Obj C} {s₁ s₂ s₃ : Obj S} → Hom C ([ T₀ ]₀ (s₁ , s₂ , ([ T₀ ]₀ (s₂ , s₃ , a)))) ([ T₀ ]₀ (s₁ , s₃ , a))}
  → {μ₁ : {a : Obj C} {s₁ s₂ s₃ : Obj S} → Hom C ([ T₁ ]₀ (s₁ , s₂ , ([ T₁ ]₀ (s₂ , s₃ , a)))) ([ T₁ ]₀ (s₁ , s₃ , a))}
  → {naturalη₀ : {s : Obj S} → {a b : Obj C} {f : Hom C a b} → [ T₀ ]₁ (id (S op) {s} , id S {s} , f) ∘C η₀ {a} {s} ≡ η₀ {b} {s} ∘C f}
  → {naturalη₁ : {s : Obj S} → {a b : Obj C} {f : Hom C a b} → [ T₁ ]₁ (id (S op) {s} , id S {s} , f) ∘C η₁ {a} {s} ≡ η₁ {b} {s} ∘C f}
  → {dinaturalη₀ : {x : Obj C} → {a b : Obj S} {f : Hom S a b} → [ T₀ ]₁ (id S {a} , f , id C {x}) ∘C η₀ {x} {a} ≡ [ T₀ ]₁ (f , id S {b} , id C {x}) ∘C η₀ {x} {b}}
  → {dinaturalη₁ : {x : Obj C} → {a b : Obj S} {f : Hom S a b} → [ T₁ ]₁ (id S {a} , f , id C {x}) ∘C η₁ {x} {a} ≡ [ T₁ ]₁ (f , id S {b} , id C {x}) ∘C η₁ {x} {b}}
  → {naturalμ₀ : {s₁ s₂ s₃ : Obj S} → {a b : Obj C} → {f : Hom C a b} 
               → [ T₀ ]₁ (id (S op) {s₁} , id S {s₃} , f) ∘C μ₀ {a} {s₁} {s₂} {s₃} ≡ μ₀ {b} {s₁} {s₂} {s₃} ∘C [ T₀ ]₁ (id (S op) {s₁} , id S {s₂} , ([ T₀ ]₁ (id (S op) {s₂} , id S {s₃} , f)))}
  → {naturalμ₁ : {s₁ s₂ s₃ : Obj S} → {a b : Obj C} → {f : Hom C a b} 
               → [ T₁ ]₁ (id (S op) {s₁} , id S {s₃} , f) ∘C μ₁ {a} {s₁} {s₂} {s₃} ≡ μ₁ {b} {s₁} {s₂} {s₃} ∘C [ T₁ ]₁ (id (S op) {s₁} , id S {s₂} , ([ T₁ ]₁ (id (S op) {s₂} , id S {s₃} , f)))}
  → {naturalμ₁₀ : {s₂ s₃ : Obj S} {x : Obj C} → {a b : Obj (S op)} {f : Hom (S op) a b} 
                → [ T₀ ]₁ (f , id S {s₃} , id C {x}) ∘C μ₀ {x} {a} {s₂} {s₃} ≡ μ₀ {x} {b} {s₂} {s₃} ∘C [ T₀ ]₁ (f , id S {s₂} , [ T₀ ]₁ (id S {s₂} ,  id S {s₃} , id C {x}))}
  → {naturalμ₁₁ : {s₂ s₃ : Obj S} {x : Obj C} → {a b : Obj (S op)} {f : Hom (S op) a b} 
                → [ T₁ ]₁ (f , id S {s₃} , id C {x}) ∘C μ₁ {x} {a} {s₂} {s₃} ≡ μ₁ {x} {b} {s₂} {s₃} ∘C [ T₁ ]₁ (f , id S {s₂} , [ T₁ ]₁ (id S {s₂} ,  id S {s₃} , id C {x}))}
  → {naturalμ₂₀ : {s₁ s₂ : Obj S} {x : Obj C} → {a b : Obj S} {f : Hom S a b} 
                → [ T₀ ]₁ (id (S op) {s₁} , f , id C {x}) ∘C μ₀ {x} {s₁} {s₂} {a} ≡ μ₀ {x} {s₁} {s₂} {b} ∘C [ T₀ ]₁ (id (S op) {s₁} , id S {s₂} , [ T₀ ]₁ (id S {s₂} , f , id C {x}))}
  → {naturalμ₂₁ : {s₁ s₂ : Obj S} {x : Obj C} → {a b : Obj S} {f : Hom S a b} 
                → [ T₁ ]₁ (id (S op) {s₁} , f , id C {x}) ∘C μ₁ {x} {s₁} {s₂} {a} ≡ μ₁ {x} {s₁} {s₂} {b} ∘C [ T₁ ]₁ (id (S op) {s₁} , id S {s₂} , [ T₁ ]₁ (id S {s₂} , f , id C {x}))}
  → {dinaturalμ₀ : {s₁ s₃ : Obj S} {x : Obj C} → {a b : Obj S} {f : Hom S a b} 
                 → μ₀ {x} {s₁} {a} {s₃} ∘C [ T₀ ]₁ (id (S op) {s₁} , id S {a} , [ T₀ ]₁ (f , id S {s₃} , id C {x})) ≡ μ₀ {x} {s₁} {b} {s₃} ∘C [ T₀ ]₁ (id (S op) {s₁} , f , [ T₀ ]₁ (id S {b} , id S {s₃} , id C {x}))}
  → {dinaturalμ₁ : {s₁ s₃ : Obj S} {x : Obj C} → {a b : Obj S} {f : Hom S a b} 
                 → μ₁ {x} {s₁} {a} {s₃} ∘C [ T₁ ]₁ (id (S op) {s₁} , id S {a} , [ T₁ ]₁ (f , id S {s₃} , id C {x})) ≡ μ₁ {x} {s₁} {b} {s₃} ∘C [ T₁ ]₁ (id (S op) {s₁} , f , [ T₁ ]₁ (id S {b} , id S {s₃} , id C {x}))}
  → {assoc₀ : ∀ {x : Obj C} {s₀ s₁ s₂ s₃ : Obj S} → μ₀ {x} {s₀} {s₁} {s₃} ∘C [ T₀ ]₁ (id S {s₀} , id S {s₁} , μ₀ {x} {s₁} {s₂} {s₃}) ≡ μ₀ {x} {s₀} {s₂} {s₃} ∘C μ₀ {[ T₀ ]₀ (s₂ , s₃ , x)} {s₀} {s₁} {s₂}}
  → {assoc₁ : ∀ {x : Obj C} {s₀ s₁ s₂ s₃ : Obj S} → μ₁ {x} {s₀} {s₁} {s₃} ∘C [ T₁ ]₁ (id S {s₀} , id S {s₁} , μ₁ {x} {s₁} {s₂} {s₃}) ≡ μ₁ {x} {s₀} {s₂} {s₃} ∘C μ₁ {[ T₁ ]₀ (s₂ , s₃ , x)} {s₀} {s₁} {s₂}}
  → {left-id₀ : {x : Obj C} {s₁ s₂ : Obj S} → μ₀ {x} {s₁} {s₂} {s₂} ∘C [ T₀ ]₁ (id (S op) {s₁} , id S {s₂} , η₀ {x} {s₂}) ≡ id C {[ T₀ ]₀ (s₁ , s₂ , x)}}
  → {left-id₁ : {x : Obj C} {s₁ s₂ : Obj S} → μ₁ {x} {s₁} {s₂} {s₂} ∘C [ T₁ ]₁ (id (S op) {s₁} , id S {s₂} , η₁ {x} {s₂}) ≡ id C {[ T₁ ]₀ (s₁ , s₂ , x)}}
  → {right-id₀ : {x : Obj C} {s₁ s₂ : Obj S} → μ₀ {x} {s₁} {s₁} {s₂} ∘C η₀ {[ T₀ ]₀ (s₁ , s₂ , x)} {s₁} ≡ id C {[ T₀ ]₀ (s₁ , s₂ , x)}}
  → {right-id₁ : {x : Obj C} {s₁ s₂ : Obj S} → μ₁ {x} {s₁} {s₁} {s₂} ∘C η₁ {[ T₁ ]₀ (s₁ , s₂ , x)} {s₁} ≡ id C {[ T₁ ]₀ (s₁ , s₂ , x)}}
  → T₀ ≡ T₁
  → (λ {a} {s} → η₀ {a} {s}) ≅ (λ {a} {s} → η₁ {a} {s})
  → (λ {a} {s₀} {s₁} {s₂} → μ₀ {a} {s₀} {s₁} {s₂}) ≅ (λ {a} {s₀} {s₁} {s₂} → μ₁ {a} {s₀} {s₁} {s₂})
  → atkey-parameterized-monad T₀ η₀ μ₀ naturalη₀ dinaturalη₀ naturalμ₀ naturalμ₁₀ naturalμ₂₀ dinaturalμ₀ assoc₀ left-id₀ right-id₀ 
  ≡ atkey-parameterized-monad T₁ η₁ μ₁ naturalη₁ dinaturalη₁ naturalμ₁ naturalμ₁₁ naturalμ₂₁ dinaturalμ₁ assoc₁ left-id₁ right-id₁ 
atkey-parameterized-monad-eq {T} {.T} {η} {.η} {μ} {.μ} {nη₀} {nη₁} {dnη₀} {dnη₁} {nμ₀} {nμ₁} {nμ₁₀} {nμ₁₁} {nμ₂₀} {nμ₂₁} {dnμ₀} {dnμ₁} {as₀} {as₁} {li₀} {li₁} {ri₀} {ri₁} refl hrefl hrefl
  = cong₉ (atkey-parameterized-monad T η μ) p1 p2 p3 p4 p5 p6 p7 p8 p9
  where
    p1 : (λ {s} {a} {b} {f} → nη₀ {s} {a} {b} {f}) ≡ nη₁
    p1 = implicit-fun-ext 
       $ λ s → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance nη₀ nη₁
         
    p2 : (λ {x} {a} {b} {f} → dnη₀ {x} {a} {b} {f}) ≡ dnη₁
    p2 = implicit-fun-ext 
       $ λ s → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance dnη₀ dnη₁
    
    p3 : (λ {s₁} {s₂} {s₃} {a} {b} {f} → nμ₀ {s₁} {s₂} {s₃} {a} {b} {f}) ≡ nμ₁
    p3 = implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → implicit-fun-ext 
       $ λ s₃ → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance nμ₀ nμ₁
    
    p4 : (λ {s₁} {s₂} {x} {a} {b} {f} → nμ₁₀ {s₁} {s₂} {x} {a} {b} {f}) ≡ nμ₁₁
    p4 = implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance nμ₁₀ nμ₁₁
    
    p5 : (λ {s₁} {s₂} {x} {a} {b} {f} → nμ₂₀ {s₁} {s₂} {x} {a} {b} {f}) ≡ nμ₂₁
    p5 = implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance nμ₂₀ nμ₂₁

    p6 : (λ {s₁} {s₂} {x} {a} {b} {f} → dnμ₀ {s₁} {s₂} {x} {a} {b} {f}) ≡ dnμ₁
    p6 = implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance dnμ₀ dnμ₁
    
    p7 : (λ {x} {s₁} {s₂} {s₃} {s₄} → as₀ {x} {s₁} {s₂} {s₃} {s₄}) ≡ as₁
    p7 = implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → implicit-fun-ext 
       $ λ s₃ → implicit-fun-ext 
       $ λ s₄ → proof-irrelevance as₀ as₁

    p8 : (λ {x} {s₁} {s₂} → li₀ {x} {s₁} {s₂}) ≡ li₁
    p8 = implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → proof-irrelevance li₀ li₁

    p9 : (λ {x} {s₁} {s₂} → ri₀ {x} {s₁} {s₂}) ≡ ri₁
    p9 = implicit-fun-ext 
       $ λ x → implicit-fun-ext 
       $ λ s₁ → implicit-fun-ext 
       $ λ s₂ → proof-irrelevance ri₀ ri₁
