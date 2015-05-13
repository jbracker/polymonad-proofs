
module Identity where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell

--------------------------------------------------------------------------------
-- Identity Type Constructor
--------------------------------------------------------------------------------

-- Pure identity type constructor
Identity : Set → Set
Identity τ = τ

-- Pure identity lift function
identity : {A : Set} → A → Identity A
identity x = x

-- Identity data type with intermediate constructor.
data IdentityC (A : Set) : Set where
  identityC : A → IdentityC A

-- Conversion from pure identity to identity data type.
id→idC : ∀ {A} → Identity A → IdentityC A
id→idC = identityC

-- Conversion from identity data type to pure identity.
idC→id : ∀ {A} → IdentityC A → Identity A
idC→id (identityC x) = x

-- Show that the relationship between both identities is indeed an isomorphism,
-- i.e., both representations are interchangable.
identityBijection : ∀ {A} → Identity A ↔ IdentityC A
identityBijection = record 
  { f   = id→idC
  ; f⁻¹ = idC→id
  ; lawf⁻¹f = refl
  ; lawff⁻¹ = prf
  } where
      prf : ∀ {A} {y : IdentityC A} → id→idC (idC→id y) ≡ y
      prf {_} {identityC y} = refl

-- Enumeration of identity type constructors for the pure identity polymonad.
data IdTyCons : Set where
  IdentTC : IdTyCons

data IdBinds : Set where
  IdentB : IdBinds

-- Bind operator for pure identity polymonad.
bindId : [ Identity , Identity ]▷ Identity
bindId x f = f x

idTC : {A : Type} → IdTyCons ⊎ A
idTC = inj₁ IdentTC

--------------------------------------------------------------------------------
-- Generalised Identity Functions
--------------------------------------------------------------------------------

id : ∀ {τ : Type} {Id : TyCon} → Id ≡ Identity → τ → Id τ
id {τ = τ} lawId x = subst (λ X → X τ) (sym lawId) x

unId : ∀ {τ : Type} {Id : TyCon} → Id ≡ Identity → Id τ → τ
unId {τ = τ} lawId x = subst (λ X → X τ) lawId x

X≡[id∘unId]X : ∀ {α : Type} {Id : TyCon} → (lawId : Id ≡ Identity) → (x : Id α) → x ≡ id lawId (unId lawId x)
X≡[id∘unId]X lawId x = x≡subst²x lawId {x = x}

X≡[id∘subst]X : ∀ {α : Type} {Id : TyCon} → (lawId : Id ≡ Identity) → (x : Id α) → x ≡ id lawId (subst (λ X → X α) lawId x)
X≡[id∘subst]X refl x = refl
