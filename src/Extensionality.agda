
-- Stdlib
open import Level renaming ( suc to lsuc )
open import Relation.Binary.HeterogeneousEquality renaming ( trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ ; sym to hsym ) -- ≅
open import Relation.Binary.PropositionalEquality -- ≡

module Extensionality where

--------------------------------------------------------------------------------
-- Function Extensionality
--------------------------------------------------------------------------------

-- We can assume function extensionality is true, because we are modelling
-- and proving things for Haskell.
postulate
  fun-ext : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} 
          → ((x : A) → f x ≡ g x) → f ≡ g

-- Function extensionality for implicit arguments
implicit-fun-ext : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} {f g : {a : A} → B a} 
                 → ((x : A) → f {x} ≡ g {x}) 
                 → (λ {a} → f {a}) ≡ (λ {a} → g {a})
implicit-fun-ext {f = f} {g = g} p = cong (λ X → (λ {a} → X a)) (fun-ext p)

-- Functions extensionality for functions with two arguments.
fun-ext₂ : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : A → Set ℓB} {C : (a : A) → B a → Set ℓC} {f g : (a : A) → (b : B a) → C a b} 
         → ((a : A) → (b : B a) → f a b ≡ g a b) 
         → f ≡ g
fun-ext₂ {f = f} {g = g} p = fun-ext (λ a → fun-ext (p a))

-- Function extensionality for heterogeneous equality.
het-fun-ext : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} 
            → ((x : A) → f x ≅ g x) 
            → f ≅ g
het-fun-ext p = ≡-to-≅ (fun-ext (λ x → ≅-to-≡ (p x)))

-- Function extensionality for heterogeneous equality with implicit arguments.
het-implicit-fun-ext : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} {f g : {a : A} → B a} 
                     → ((x : A) → f {x} ≅ g {x}) 
                     → (λ {a} → f {a}) ≅ (λ {a} → g {a})
het-implicit-fun-ext {f = f} {g = g} p = hcong (λ X → (λ {a} → X a)) (het-fun-ext p)
