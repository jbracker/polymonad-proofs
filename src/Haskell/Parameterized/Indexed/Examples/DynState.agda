
module Haskell.Parameterized.Indexed.Examples.DynState where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Vec hiding ( _>>=_ ; _∈_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Haskell.Parameterized.Indexed.Monad
open import Haskell.Parameterized.PhantomIndices  

-- -----------------------------------------------------------------------------
-- Definition of the dynamic state monad
-- -----------------------------------------------------------------------------

record DynState (i : Type) (j : Type) (α : Type) : Type where
  constructor DynStateCon
  field
    stateFun : i → j × α

runDynState : {i j α : Type} → DynState i j α → i → j × α
runDynState (DynStateCon sf) i = sf i

execDynState : {i j α : Type} → DynState i j α → i → j
execDynState ma i = proj₁ (runDynState ma i)

evalDynState : {i j α : Type} → DynState i j α → i → α
evalDynState ma i = proj₂ (runDynState ma i)

DynStateMonad : IxMonad Type DynState
DynStateMonad = record
  { _>>=_ = _>>=_
  ; return = return
  ; functor = λ i j → record 
    { fmap = λ f ma → ma >>= (return ∘ f)
    ; law-id = refl
    ; law-compose = λ f g → refl
    }
  ; law-right-id = λ a k → refl
  ; law-left-id = λ m → refl
  ; law-assoc = λ m f g → refl
  ; law-monad-fmap = λ f ma → refl
  } where
    _>>=_ : {α β i j k : Type} → DynState i j α → (α → DynState j k β) → DynState i k β
    _>>=_ ma f = DynStateCon (λ i → let j , a = runDynState ma i in runDynState (f a) j)
    
    return : {α i : Type} → α → DynState i i α
    return a = DynStateCon (λ s → s , a)

-- -----------------------------------------------------------------------------
-- Lifting the universe of DynState
-- -----------------------------------------------------------------------------

LiftDynState : ∀ {ℓ} → Type → Type → Lift {ℓ = ℓ} TyCon
LiftDynState I J = lift (DynState I J)

liftDynStateShift : ∀ {ℓ} {I J : Type} → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ DynState I J
liftDynStateShift = refl

liftDynStateShiftEq : ∀ {ℓ} {I J K L : Type} → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} K L) → DynState I J ≡ DynState K L
liftDynStateShiftEq eq = eq

liftDynStateShiftEq' : ∀ {ℓ} {I J K L : Type} → DynState I J ≡ DynState K L → lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} I J) ≡ lower {ℓ = ℓ} (LiftDynState {ℓ = ℓ} K L)
liftDynStateShiftEq' eq = eq

-- -----------------------------------------------------------------------------
-- Lemmas about dynamic state monads
-- -----------------------------------------------------------------------------

{-
PhantomIndices : ∀ {ℓ} {n} (ts : Vec (Set ℓ) n) → (M : ParamTyCon ts) → Set (lsuc ℓ)
PhantomIndices {ℓ = ℓ} ts M = ∃ λ(K : TyCon) → ∀Indices ts M (λ X → Lift {ℓ = lsuc ℓ} (X ≡ K))

NonPhantomIndices : ∀ {ℓ} {n} (ts : Vec (Set ℓ) n) → (M : ParamTyCon ts) → Set (lsuc ℓ)
NonPhantomIndices {ℓ = ℓ} ts M = ∃Indices ts M (λ X → ∃Indices ts M (λ Y → Lift {ℓ = lsuc ℓ} (¬ X ≡ Y)))
-}

{-
DynState→¬PhantomIndices : ∀ (i j : Type) → ¬ i ≡ j → ¬ PhantomIndices (Type ∷ Type ∷ []) LiftDynState
DynState→¬PhantomIndices i j ¬i≡j pa = ¬i≡j (proj₂ {!pa!})
  where
    A : ∀ {ℓ} → Lift {ℓ = ℓ} TyCon
    A = LiftDynState i i
    
    B : ∀ {ℓ} → Lift {ℓ = ℓ} TyCon
    B = LiftDynState i j
    
    funEq : ∀ {ℓ} {α β γ δ : Set ℓ} 
          → (α ≡ γ) → (β ≡ δ) 
          → (α → β) ≡ (γ → δ)
    funEq refl refl = refl
    
    prodEq : ∀ {ℓ} {α β γ δ : Set ℓ} 
           → (α ≡ γ) → (β ≡ δ) 
           → (α × β) ≡ (γ × δ)
    prodEq refl refl = refl
    
    prodEq2 : ∀ {ℓ} {α β γ δ : Set ℓ} 
           → (α × β) ≡ (γ × δ)
           → (α ≡ γ) × (β ≡ δ) 
    prodEq2 {α = α} {β = β} eq with (α × β)
    prodEq2 {γ = γ} {δ = δ} eq | p with (γ × δ)
    prodEq2 refl | q | .q = {!refl!} , {!!}
    
    proof1 : ∀ {α i j k l : Type} 
           → DynState i j α → DynState k l α 
           → (¬ (i ≡ k) ⊎ ¬ (j ≡ l))
           → ¬ (DynState i j α ≡ DynState k l α)
    proof1 (DynStateCon sf₁) (DynStateCon sf₂) (inj₁ ¬i≡k) eqDS = {!!}
    proof1 ma mb (inj₂ ¬j≡l) eqDS = {!!}
    
    proof : ∀ {α : Type} {i j k l : Type} → DynState i j α ≡ DynState k l α → i ≡ k × j ≡ l
    proof {α = α} {i = i} {j = j} prf with DynState i j α
    proof {α = α} {k = k} {l = l} prf | p with DynState k l α 
    proof refl | p | .p = {!!} , {!!}
    
    ¬A≡B : ∀ {α : Type} → (i j : Type) → ¬ i ≡ j → ¬ DynState i j α ≡ DynState i i α
    ¬A≡B {α} i j ¬i≡j Dij≡Dii with DynState i j α
    ¬A≡B {α} i j ¬i≡j Dij≡Dii | p with DynState i i α 
    ¬A≡B i j ¬i≡j refl | q | .q = {!!}

DynState→NonPhantomIndices : NonPhantomIndices (Type ∷ Type ∷ []) LiftDynState
DynState→NonPhantomIndices = ⊤ , ⊤ , ⊤ , ⊥ , lift (λ x → {!!})
-}
