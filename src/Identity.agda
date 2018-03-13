
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
open import Bijection using ( _↔_ )
open import Haskell

--------------------------------------------------------------------------------
-- Identity Type Constructor
--------------------------------------------------------------------------------

-- Pure identity type constructor.
Identity : TyCon
Identity τ = τ

-- Pure identity function.
identity : {A : Set} → A → Identity A
identity x = x

-- Identity data type with intermediate constructor.
data IdentityC (A : Set) : Set where
  identityC : A → IdentityC A

-- Conversion from pure identity to identity data type.
id→idC : ∀ {A} → Identity A → IdentityC A
id→idC x = identityC x

-- Conversion from identity data type to pure identity.
idC→id : ∀ {A} → IdentityC A → Identity A
idC→id (identityC x) = x

-- Show that the relationship between both identities is indeed an isomorphism,
-- i.e., both representations are interchangable.
identity-bijection : ∀ {α} → Identity α ↔ IdentityC α
identity-bijection {α = α} = record
  { f   = id→idC
  ; inv = idC→id
  ; right-id = right-id
  ; left-id = λ a → refl
  } where
      right-id : (b : IdentityC α) → id→idC (idC→id b) ≡ b
      right-id (identityC b) = refl

-- Enumeration of identity type constructors for the pure identity polymonad.
data IdTyCons : Set where
  IdentTC : IdTyCons

data IdBinds {n} : Set n where
  IdentB : IdBinds

-- Bind operator for pure identity polymonad.
bindId : [ Identity , Identity ]▷ Identity
bindId x f = f x

idTC : ∀ {n} {A : Set n} → IdTyCons ⊎ A
idTC = inj₁ IdentTC

--------------------------------------------------------------------------------
-- Generalised Identity Functions
--------------------------------------------------------------------------------

-- Identity Kleisli-arrow that is polymorphic over the identity type constructor.
id : ∀ {τ : Type} {Id : TyCon} → Id ≡ Identity → τ → Id τ
id {τ = τ} law-id x = subst (λ X → X τ) (sym law-id) x

unId : ∀ {τ : Type} {Id : TyCon} → Id ≡ Identity → Id τ → τ
unId {τ = τ} law-id x = subst (λ X → X τ) law-id x

X≡[id∘unId]X : ∀ {α : Type} {Id : TyCon} → (law-id : Id ≡ Identity) → (x : Id α) → x ≡ id law-id (unId law-id x)
X≡[id∘unId]X {α = α} law-id x = sym (subst²≡id' law-id (λ X → X α) x)

X≡[id∘subst]X : ∀ {α : Type} {Id : TyCon} → (law-id : Id ≡ Identity) → (x : Id α) → x ≡ id law-id (subst (λ X → X α) law-id x)
X≡[id∘subst]X refl x = refl
