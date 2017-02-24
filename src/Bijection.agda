
open import Level
open import Function

open import Data.Sum
open import Data.Product

open import Relation.Binary.Core using ( IsEquivalence )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; proof-irrelevance ) renaming ( refl to prefl ; sym to psym ; trans to ptrans ; cong to pcong ; cong₂ to pcong₂ )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ) renaming ( refl to hrefl )

open import Extensionality

module Bijection where

--------------------------------------------------------------------------------
-- Definition of Bijections
--------------------------------------------------------------------------------
record Bijection {ℓA ℓB : Level} (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
  constructor bijection
  
  field
    f : A → B
    inv : B → A
    
  f⁻¹ = inv
  
  field
    right-id : (b : B) → f (f⁻¹ b) ≡ b
    left-id  : (a : A) → f⁻¹ (f a) ≡ a
  
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  
  law-injective : (a b : A) → f a ≡ f b → a ≡ b
  law-injective a b fa≡fb = begin 
    a 
      ≡⟨ sym (left-id a) ⟩ 
    f⁻¹ (f a) 
      ≡⟨ cong f⁻¹ fa≡fb ⟩
    f⁻¹ (f b)
      ≡⟨ left-id b ⟩
    b ∎
  
  law-injective-inv : (a b : B) → f⁻¹ a ≡ f⁻¹ b → a ≡ b
  law-injective-inv a b fa≡fb = begin
    a 
      ≡⟨ sym (right-id a) ⟩ 
    f (f⁻¹ a) 
      ≡⟨ cong f fa≡fb ⟩
    f (f⁻¹ b)
      ≡⟨ right-id b ⟩
    b ∎
  
  law-surjective : ∀ (b : B) → ∃ λ (a : A) → (f a) ≡ b
  law-surjective b = f⁻¹ b , right-id b
  
  law-surjective-inv : ∀ (a : A) → ∃ λ (b : B) → (f⁻¹ b) ≡ a
  law-surjective-inv a = f a , left-id a

_↔_ = Bijection

open Bijection

--------------------------------------------------------------------------------
-- Propositional equality of bijections
--------------------------------------------------------------------------------
private
  module Equality {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} where
    
    unique-inverse : (A↔B₀ A↔B₁ : A ↔ B) → f A↔B₀ ≡ f A↔B₁ → inv A↔B₀ ≡ inv A↔B₁
    unique-inverse (bijection f  inv₀ right-id₀ left-id₀) 
                   (bijection .f inv₁ right-id₁ left-id₁)
                   prefl = fun-ext inv-eq
      where
        inv-eq : (b : B) → inv₀ b ≡ inv₁ b
        inv-eq b with law-surjective (bijection f inv₀ right-id₀ left-id₀) b
        inv-eq .(f a) | a , prefl = ptrans (left-id₀ a) (psym $ left-id₁ a)
    
    unique-function : (A↔B₀ A↔B₁ : A ↔ B) → inv A↔B₀ ≡ inv A↔B₁ → f A↔B₀ ≡ f A↔B₁
    unique-function (bijection f₀ inv  right-id₀ left-id₀) 
                    (bijection f₁ .inv right-id₁ left-id₁)
                    prefl = fun-ext f-eq
      where
        f-eq : (a : A) → f₀ a ≡ f₁ a
        f-eq a with law-surjective-inv (bijection f₀ inv right-id₀ left-id₀) a
        f-eq .(inv b) | b , prefl = ptrans (right-id₀ b) (psym $ right-id₁ b)
    
    bijection-eq : {f₀ : A → B} → {f₁ : A → B}
                 → {inv₀ : B → A} → {inv₁ : B → A}
                 → {right-id₀ : (b : B) → f₀ (inv₀ b) ≡ b}
                 → {right-id₁ : (b : B) → f₁ (inv₁ b) ≡ b}
                 → {left-id₀ : (a : A) → inv₀ (f₀ a) ≡ a}
                 → {left-id₁ : (a : A) → inv₁ (f₁ a) ≡ a}
                 → (f₀ ≡ f₁) ⊎ (inv₀ ≡ inv₁)
                 → bijection f₀ inv₀ right-id₀ left-id₀ ≡ bijection f₁ inv₁ right-id₁ left-id₁
    bijection-eq {f₀ = f } {.f} {inv₀} {inv₁} {right-id₀} {right-id₁} {left-id₀} {left-id₁} (inj₁ prefl) 
      with unique-inverse (bijection f inv₀ right-id₀ left-id₀) (bijection f inv₁ right-id₁ left-id₁) prefl
    bijection-eq {f₀ = f } {.f} {inv } {.inv} {right-id₀} {right-id₁} {left-id₀} {left-id₁} (inj₁ prefl) | prefl 
      = pcong₂ (bijection f inv) 
               (fun-ext (λ b → proof-irrelevance (right-id₀ b) (right-id₁ b))) 
               (fun-ext (λ a → proof-irrelevance (left-id₀  a) (left-id₁  a)))
    bijection-eq {f₀ = f₀} {f₁} {inv } {.inv} {right-id₀} {right-id₁} {left-id₀} {left-id₁} (inj₂ prefl)
      with unique-function (bijection f₀ inv right-id₀ left-id₀) (bijection f₁ inv right-id₁ left-id₁) prefl
    bijection-eq {f₀ = f } {.f} {inv } {.inv} {right-id₀} {right-id₁} {left-id₀} {left-id₁} (inj₂ prefl) | prefl
      = pcong₂ (bijection f inv) 
               (fun-ext (λ b → proof-irrelevance (right-id₀ b) (right-id₁ b))) 
               (fun-ext (λ a → proof-irrelevance (left-id₀  a) (left-id₁  a)))

open Equality public

--------------------------------------------------------------------------------
-- Definition of the equivalence created by bijections
--------------------------------------------------------------------------------

refl : {ℓA : Level} {A : Set ℓA} → A ↔ A
refl = record 
  { f = id
  ; inv = id
  ; right-id = λ _ → prefl
  ; left-id = λ _ → prefl
  }

sym : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB}
              → A ↔ B → B ↔ A
sym A↔B = record 
  { f = inv A↔B 
  ; inv = f A↔B 
  ; right-id = left-id A↔B
  ; left-id = right-id A↔B
  }

trans : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
                → A ↔ B → B ↔ C → A ↔ C
trans A↔B B↔C = record 
  { f = f B↔C ∘ f A↔B
  ; inv = inv A↔B ∘ inv B↔C
  ; right-id = λ c → ptrans (pcong (f B↔C) (right-id A↔B (inv B↔C c))) (right-id B↔C c)
  ; left-id = λ a → ptrans (pcong (inv A↔B) (left-id B↔C (f A↔B a))) (left-id A↔B a)
  }

≡-to-↔ : {ℓ : Level} {A B : Set ℓ} → A ≡ B → A ↔ B
≡-to-↔ prefl = refl

≅-to-↔ : {ℓ : Level} {A B : Set ℓ} → A ≅ B → A ↔ B
≅-to-↔ hrefl = refl

bijection-equivalence : {ℓ : Level} → IsEquivalence (Bijection {ℓ} {ℓ})
bijection-equivalence {ℓ} = record 
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

--------------------------------------------------------------------------------
-- Definition reasoning EDSL for bijections
--------------------------------------------------------------------------------
module ↔-Reasoning where
  
  infix  3 _∎
  infixr 2 _↔⟨⟩_ _↔⟨_⟩_ _≡⟨_⟩_ _≅⟨_⟩_
  infix  1 begin_

  begin_ : ∀ {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → A ↔ B → A ↔ B
  begin_ A↔B = A↔B

  _↔⟨⟩_ : ∀ {ℓA ℓB : Level} (A : Set ℓA) {B : Set ℓB} → A ↔ B → A ↔ B
  _ ↔⟨⟩ A↔B = A↔B

  _↔⟨_⟩_ : ∀ {ℓA ℓB ℓC : Level} (A : Set ℓA) {B : Set ℓB} {C : Set ℓC} 
         → A ↔ B → B ↔ C → A ↔ C
  _ ↔⟨ A↔B ⟩ B↔C = trans A↔B B↔C

  _≡⟨_⟩_ : ∀ {ℓA ℓC : Level} (A {B} : Set ℓA) {C : Set ℓC}
          → A ≡ B → B ↔ C → A ↔ C
  _ ≡⟨ prefl ⟩ B↔C = trans refl B↔C
  
  _≅⟨_⟩_ : ∀ {ℓA ℓC : Level} (A {B} : Set ℓA) {C : Set ℓC} 
          → A ≅ B → B ↔ C → A ↔ C
  _ ≅⟨ hrefl ⟩ B↔C = trans refl B↔C
  
  _∎ : ∀ {ℓA : Level} (A : Set ℓA) → A ↔ A
  _∎ _ = refl
