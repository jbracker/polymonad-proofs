
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.Product hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )
open import Relation.Binary using ( Decidable ; IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open ≡-Reasoning

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell.Applicative using ( _***_ )

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )

open import Theory.Functor.Definition

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Applicative

module Theory.Haskell.Constrained.GeneralRulesForConstrainedCategories {ℓ : Level} where 

-- General proof that a few simple assumptions about constraints already delivers an appropriate constraint category.
postulate
  CtObj : Set ℓ → Set (suc ℓ)
  CtHom : Set ℓ → Set ℓ → Set (suc ℓ)

  idCt : {α : Set ℓ} → CtHom α α
  _∘Ct_ : {α β γ : Set ℓ} → CtHom β γ → CtHom α β → CtHom α γ

  eqCt : {α β : Set ℓ} → (ct-a ct-b : CtHom α β) → ct-a ≡ ct-b

CtCat : DependentCategory {ℓ₀ = suc ℓ} {ℓ₁ = ℓ} {ℓDep₀ = suc ℓ} {ℓDep₁ = suc ℓ} (SetCat {ℓ})
CtCat = dependentCategory CtObj CtHom' _∘Ct_ idCt
  (λ ct-f ct-g ct-h → ≡-to-≅ (eqCt (ct-h ∘Ct (ct-g ∘Ct ct-f)) ((ct-h ∘Ct ct-g) ∘Ct ct-f)))
  (λ ct-f → ≡-to-≅ (eqCt (idCt ∘Ct ct-f) ct-f))
  (λ ct-f → ≡-to-≅ (eqCt (ct-f ∘Ct idCt) ct-f))
  where
    CtHom' : {α β : Set ℓ} → CtObj α → CtObj β → (α → β) → Set (suc ℓ)
    CtHom' {α} {β} (ct-α) (ct-β) f = CtHom α β

⊤' = Lift {zero} {ℓ} ⊤

postulate
  _×CtObj_ : {α β : Set ℓ} → CtObj α → CtObj β → CtObj (α × β)
  _×CtHom_ : {α β γ δ : Set ℓ} → CtHom α β → CtHom γ δ → CtHom (α × γ) (β × δ)

  unitCt : CtObj ⊤'

  assocCt     : {α β γ : Set ℓ} → CtObj α → CtObj β → CtObj γ → CtHom ((α × β) × γ) (α × (β × γ))
  assocCt-inv : {α β γ : Set ℓ} → CtObj α → CtObj β → CtObj γ → CtHom (α × (β × γ)) ((α × β) × γ)
  
  leftIdCt     : {α : Set ℓ} → CtObj α → CtHom (⊤' × α) α
  leftIdCt-inv : {α : Set ℓ} → CtObj α → CtHom α (⊤' × α)
  
  rightIdCt     : {α : Set ℓ} → CtObj α → CtHom (α × ⊤') α
  rightIdCt-inv : {α : Set ℓ} → CtObj α → CtHom α (α × ⊤')

  

_×F_ : {α β γ δ : Set ℓ} → (α → β) → (γ → δ) → (α × γ → β × δ)
_×F_ f g (a , c) = f a , g c

_×CtHom'_ : {α β γ δ : Set ℓ} → (Σ (α → β) (λ _ → CtHom α β)) → (Σ (γ → δ) (λ _ → CtHom γ δ)) → (Σ (α × γ → β × δ) (λ _ → CtHom (α × γ) (β × δ)))
_×CtHom'_ {α} {β} {γ} {δ} (f , ct-αβ) (g , ct-γδ) = (f ×F g) , (ct-αβ ×CtHom ct-γδ)

CtMonCat : DependentMonoidalCategory (SetMonCat {ℓ})
CtMonCat = record
  { DC = CtCat
  ; _Dep⊗₀_ = _×CtObj_
  ; _Dep⊗₁_ = _×CtHom_
  ; depUnit = unitCt
  ; dep-tensor-id = λ {α} {β} {ct-α} {ct-β} →
                      ≡-to-≅ (eqCt (idCt {α} ×CtHom idCt {β}) (idCt {α × β}))
  ; dep-tensor-compose = λ {α} {β} {γ} {δ} {ε} {ι} {ct-α} {ct-β} {ct-γ} {ct-δ} {ct-ε} {ct-ι} {f} {g} {h} {k} {ct-f} {ct-g} {ct-h} {ct-k} →
                           ≡-to-≅ (eqCt ((ct-h ∘Ct ct-f) ×CtHom (ct-k ∘Ct ct-g)) ((ct-h ×CtHom ct-k ) ∘Ct (ct-f ×CtHom ct-g)))
  ; dep-α = assocCt
  ; dep-α-inv = assocCt-inv
  ; dep-λ = leftIdCt
  ; dep-λ-inv = leftIdCt-inv
  ; dep-ρ = rightIdCt
  ; dep-ρ-inv = rightIdCt-inv
  ; dep-α-natural = λ {α} {β} {γ} {δ} {ε} {ι} {ct-α} {ct-β} {ct-γ} {ct-δ} {ct-ε} {ct-ι} {f} {g} {h} {ct-f} {ct-g} {ct-h} →
                      ≡-to-≅ (eqCt ((ct-f ×CtHom (ct-g ×CtHom ct-h)) ∘Ct (assocCt ct-α ct-β ct-γ)) ((assocCt ct-δ ct-ε ct-ι) ∘Ct ((ct-f ×CtHom ct-g) ×CtHom ct-h)))
  ; dep-λ-natural = λ {α} {β} {ct-α} {ct-β} {f} {ct-f} →
                      ≡-to-≅ (eqCt (ct-f ∘Ct leftIdCt ct-α) (leftIdCt ct-β ∘Ct (idCt ×CtHom ct-f)))
  ; dep-ρ-natural = λ {α} {β} {ct-α} {ct-β} {f} {ct-f} →
                      ≡-to-≅ (eqCt (ct-f ∘Ct rightIdCt ct-α) (rightIdCt ct-β ∘Ct (ct-f ×CtHom idCt)))
  ; dep-α-left-id = λ {α} {β} {γ} ct-α ct-β ct-γ →
                      ≡-to-≅ (eqCt (assocCt ct-α ct-β ct-γ ∘Ct assocCt-inv ct-α ct-β ct-γ) idCt)
  ; dep-α-right-id = λ {α} {β} {γ} ct-α ct-β ct-γ →
                       ≡-to-≅ (eqCt (assocCt-inv ct-α ct-β ct-γ ∘Ct assocCt ct-α ct-β ct-γ) idCt)
  ; dep-λ-left-id = λ {α} ct-α →
                      ≡-to-≅ (eqCt (leftIdCt ct-α ∘Ct leftIdCt-inv ct-α) idCt)
  ; dep-λ-right-id = λ {α} ct-α →
                       ≡-to-≅ (eqCt (leftIdCt-inv ct-α ∘Ct leftIdCt ct-α) idCt)
  ; dep-ρ-left-id = λ {α} ct-α →
                      ≡-to-≅ (eqCt (rightIdCt ct-α ∘Ct rightIdCt-inv ct-α) idCt)
  ; dep-ρ-right-id = λ {α} ct-α →
                       ≡-to-≅ (eqCt (rightIdCt-inv ct-α ∘Ct rightIdCt ct-α) idCt)
  ; dep-triangle-id = λ {α} {β} ct-α ct-β →
                        ≡-to-≅ (eqCt (rightIdCt ct-α ×CtHom idCt) ((idCt ×CtHom leftIdCt ct-β) ∘Ct (assocCt ct-α unitCt ct-β)))
  ; dep-pentagon-id = λ {α} {β} {γ} {δ} ct-α ct-β ct-γ ct-δ →
                        ≡-to-≅ (eqCt ((idCt ×CtHom assocCt ct-β ct-γ ct-δ) ∘Ct ((assocCt ct-α (ct-β ×CtObj ct-γ) ct-δ) ∘Ct (assocCt ct-α ct-β ct-γ ×CtHom idCt)))
                                     (assocCt ct-α ct-β (ct-γ ×CtObj ct-δ) ∘Ct assocCt (ct-α ×CtObj ct-β) ct-γ ct-δ))
  }
