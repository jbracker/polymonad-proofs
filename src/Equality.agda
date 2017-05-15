
open import Level

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl )

module Equality where

-------------------------------------------------------------------------------
-- Equality of Σ-types
-------------------------------------------------------------------------------
private
  module Product where
    open import Data.Product
    Σ-eq : {ℓA ℓB : Level}
         → {A : Set ℓA} {B : A → Set ℓB}
         → {a₀ a₁ : A} → a₀ ≡ a₁ 
         → {b₀ : B a₀} {b₁ : B a₁} → b₀ ≅ b₁
         → (a₀ , b₀) ≡ (a₁ , b₁)
    Σ-eq refl hrefl = refl

    het-Σ-eq : {ℓA ℓB : Level}
         → {A : Set ℓA} {B : A → Set ℓB}
         → {a₀ a₁ : A} → a₀ ≡ a₁ 
         → {b₀ : B a₀} {b₁ : B a₁} → b₀ ≅ b₁
         → _,_ {B = B} a₀ b₀ ≅ _,_ {B = B} a₁ b₁
    het-Σ-eq refl hrefl = hrefl
open Product public
