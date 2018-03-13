
module Utilities where

-- Stdlib
open import Level
open import Function
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary -- ¬
open import Relation.Binary.HeterogeneousEquality renaming ( trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ ; sym to hsym ) -- ≅
open import Relation.Binary.PropositionalEquality -- ≡
open ≡-Reasoning

--------------------------------------------------------------------------------
-- Uniqueness of something
--------------------------------------------------------------------------------

IsUnique : {ℓ : Level} {A : Set ℓ} → (a : A) → Set ℓ
IsUnique {ℓ} {A} a = ∀ (b : A) → b ≡ a

--------------------------------------------------------------------------------
-- Formalization of Subsets
--------------------------------------------------------------------------------

-- Formalization of a subsets for a given set.
SubsetOf : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
SubsetOf {ℓ} X = X → Set ℓ

-- An element is in the subset, if the subset predicate is true.
_∈_ : ∀ {ℓ} {X : Set ℓ} → (x : X) → (S : SubsetOf X) → Set ℓ
x ∈ S = S x

--------------------------------------------------------------------------------
-- Formalization of Injectivity and Surjectivity
--------------------------------------------------------------------------------

private
  module FunctionProperties {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} (F : A → B) where

    IsInjective :  Set (ℓA ⊔ ℓB)
    IsInjective = (x y : A) → F x ≡ F y → x ≡ y

    IsSurjective : Set (ℓA ⊔ ℓB)
    IsSurjective = (y : B) → ∃ λ (x : A) → F x ≡ y

    IsBijective : Set (ℓA ⊔ ℓB)
    IsBijective = IsInjective × IsSurjective

open FunctionProperties public

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- Disprove a proposition by providing a counterexample.
counterexample : ∀ {k l} {A : Set k} {P : A → Set l}
           → (((a : A) → P a) → ∃ λ(a : A) → ¬ (P a)) 
           → ¬ ((a : A) → P a)
counterexample ce P = let a , ¬Pa = ce P in ¬Pa (P a)

-- If two type functions are equivalent, then applying them to the same value 
-- delivers equivalent results.
funCong : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {f g : A → Set ℓ₁} → f ≡ g → {a : A} → f a ≡ g a
funCong {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A} {f} {g} fg {a} = cong {a = suc ℓ₁ ⊔ ℓ₀} (λ h → h a) fg

funCong₂ : ∀ {A B C : Set} {a : A} {b : B} {f g : A → B → C} → f ≡ g → f a b ≡ g a b
funCong₂ {a = a} {b} {f} {g} fg = cong (λ h → h a b) fg

-- Two substitutions next to each other that reverse their effect, can be removed.
subst²≡id : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {p q : A}
          → (eq : p ≡ q)
          → (F : A → Set ℓ₂)
          → (x : F q)
          → subst F eq (subst F (sym eq) x) ≡ x 
subst²≡id refl F x = refl

subst²≡id' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {p q : A}
           → (eq : q ≡ p)
           → (F : A → Set ℓ₂)
           → (x : F q)
           → subst F (sym eq) (subst F eq x) ≡ x
subst²≡id' refl F x = refl

substTrans : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {q p o : A}
           → (eqA : q ≡ p)
           → (eqB : p ≡ o)
           → (F : A → Set ℓ₂)
           → (x : F q)
           → subst F eqB (subst F eqA x) ≡ subst F (trans eqA eqB) x
substTrans refl refl F x = refl

subst₂²≡id1 : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {p q : A} {s t : B}
            → (eq₁ : p ≡ q)
            → (eq₂ : t ≡ s)
            → (F : A → B → Set ℓ₃)
            → (x : F q s)
            → subst₂ F eq₁ eq₂ (subst₂ F (sym eq₁) (sym eq₂) x) ≡ x
subst₂²≡id1 refl refl F x = refl

-- The laws involving the existance of certains bind operators 
-- are simplified using the curry-howard correspondance:
-- ∃ λ A → ⊤   ⇔   A
-- (a , tt)    ⇔   a
-- and
-- ∃ λ A → ∃ λ B → ⊤   ⇔   A × B
-- (a, (b, tt))        ⇔   a , b
curry-∃→ : ∀ {A : Set} → (∃ λ A → ⊤) → A
curry-∃→ (a , tt) = a

curry-∃← : ∀ {A : Set} → A → (∃ λ A → ⊤)
curry-∃← a = a , tt

curry-∃∃→ : ∀ {A B : Set} → (∃ λ A → ∃ λ B → ⊤) → A × B
curry-∃∃→ (a , (b , tt)) = a , b

curry-∃∃← : ∀ {A B : Set} → A × B → (∃ λ A → ∃ λ B → ⊤)
curry-∃∃← (a , b) = (a , (b , tt))

-- Equivalence of negation of existence and forall.
¬∃→∀¬ : (A : Set) → (P : A → Set) → ¬ (∃ λ(a : A) → P a) → (∀ (a : A) → ¬ P a)
¬∃→∀¬ A P p a pa = p (a , pa)

∀¬→¬∃ : (A : Set) → (P : A → Set) → (∀ (a : A) → ¬ P a) → ¬ (∃ λ(a : A) → P a)
∀¬→¬∃ A P p (a , pa) = p a pa

