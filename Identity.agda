
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
identityBijection : ∀ {α} → Identity α ↔ IdentityC α
identityBijection {α = α} = record
  { f   = id→idC
  ; f⁻¹ = idC→id
  ; lawInjective    = λ a₁ a₂ prf → cong (λ X → idC→id X) prf
  ; lawSurjective   = surjective
  ; lawInjective⁻¹  = injective⁻¹
  ; lawSurjective⁻¹ = λ a → refl
  } where
      surjective : ∀ (a : IdentityC α) → id→idC (idC→id a) ≡ a
      surjective (identityC a) = refl
      
      injective⁻¹ : (b₁ b₂ : IdentityC α) → idC→id b₁ ≡ idC→id b₂ → b₁ ≡ b₂
      injective⁻¹ (identityC b₁) (identityC b₂) prf = begin
        identityC b₁ 
          ≡⟨ refl ⟩
        id→idC (idC→id (identityC b₁))
          ≡⟨ cong (λ X → id→idC X) prf ⟩
        id→idC (idC→id (identityC b₂))
          ≡⟨ refl ⟩
        identityC b₂ ∎



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
id {τ = τ} lawId x = subst (λ X → X τ) (sym lawId) x

unId : ∀ {τ : Type} {Id : TyCon} → Id ≡ Identity → Id τ → τ
unId {τ = τ} lawId x = subst (λ X → X τ) lawId x

X≡[id∘unId]X : ∀ {α : Type} {Id : TyCon} → (lawId : Id ≡ Identity) → (x : Id α) → x ≡ id lawId (unId lawId x)
X≡[id∘unId]X lawId x = x≡subst²x lawId {x = x}

X≡[id∘subst]X : ∀ {α : Type} {Id : TyCon} → (lawId : Id ≡ Identity) → (x : Id α) → x ≡ id lawId (subst (λ X → X α) lawId x)
X≡[id∘subst]X refl x = refl
