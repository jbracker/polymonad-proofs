 
module Haskell where

-- StdLib
open import Level renaming ( zero to lzero)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Theory.Examples.Category

--------------------------------------------------------------------------------
-- Type Synonyms
--------------------------------------------------------------------------------

-- Types are sets of values in Haskell.
Type : Set₁
Type = Set

-- Unary type constructors take one type and produce another one.
TyCon : Set₁
TyCon = Type → Type

-- Short-hand notation for bind-operation type signatures as used in the paper.
[_,_]▷_ : (M N P : TyCon) → Set₁
[ M , N ]▷ P = (∀ {α β : Type} → (M α → (α → N β) → P β))

--------------------------------------------------------------------------------
-- What we assume to be the category of Haskell
--------------------------------------------------------------------------------

Hask = setCategory {lzero}

--------------------------------------------------------------------------------
-- Some general equality laws
--------------------------------------------------------------------------------

substBind :  ∀ {M₂ N₂ P₂ M₁ N₁ P₁ : TyCon}
          → M₁ ≡ M₂ → N₁ ≡ N₂ → P₁ ≡ P₂ 
          → [ M₁ , N₁ ]▷ P₁ → [ M₂ , N₂ ]▷ P₂
substBind {M₂} {N₂} {P₂} {M₁} {N₁} {P₁} eqM eqN eqP b = 
  subst (λ x → [ x , N₂ ]▷ P₂) eqM 
        (subst (λ x → [ M₁ , x ]▷ P₂) eqN 
               (subst (λ x → [ M₁ , N₁ ]▷ x) eqP b))

b≡substBind²b : ∀ {M N P M' N' P' : TyCon} 
              → (b : [ M , N ]▷ P)
              → (eqM : M ≡ M')
              → (eqN : N ≡ N')
              → (eqP : P ≡ P')
              → ∀ {α β : Type}
              → b {α} {β} ≡ substBind (sym eqM) (sym eqN) (sym eqP) (substBind eqM eqN eqP b)
b≡substBind²b b refl refl refl = refl
                                       
substBindInwardEq : ∀ {M N P M' N' P' : TyCon}
                  → (b : [ M , N ]▷ P)
                  → (eqM : M ≡ M') → (eqN : N ≡ N') → (eqP : P ≡ P')
                  → ∀ {α β : Type}
                  → (m : M' α) → (f : α → N' β)
                  → (substBind eqM eqN eqP b) m f
                  ≡ subst (λ P → P β) eqP (b (subst (λ M → M α) (sym eqM) m) (subst (λ N → (α → N β)) (sym eqN) f)) 
substBindInwardEq b refl refl refl m f = refl

substBindInwardEqF : ∀ {M N P M' N' P' : TyCon}
                   → (b : [ M , N ]▷ P)
                   → (eqM : M ≡ M') → (eqN : N ≡ N') → (eqP : P ≡ P')
                   → ∀ {α β γ : Type}
                   → (m : γ → M' α) → (f : α → N' β)
                   → (λ x → (substBind eqM eqN eqP b) (m x) f)
                   ≡ (λ x → subst (λ P → P β) eqP (b (subst (λ M → M α) (sym eqM) (m x)) (subst (λ N → (α → N β)) (sym eqN) f))) 
substBindInwardEqF b refl refl refl m f = refl

shiftApplySubst : ∀ {M M' : TyCon}
                → (eqM : M ≡ M')
                → ∀ {α β : Type}
                → (v : α) → (f : α → M β)
                → (subst (λ M → (α → M β)) eqM f) v ≡ subst (λ M → M β) eqM (f v)
shiftApplySubst refl v f = refl

shiftApplySubstF : ∀ {M M' : TyCon}
                 → (eqM : M ≡ M')
                 → ∀ {α β γ : Type}
                 → (P : M' β → γ) → (f : α → M β)
                 → (λ v → P ((subst (λ M → (α → M β)) eqM f) v)) ≡ (λ v → P (subst (λ M → M β) eqM (f v)))
shiftApplySubstF refl P f = refl

shiftFunSubst : ∀ {M M' : TyCon}
              → (eqM : M ≡ M')
              → ∀ {α β : Type}
              → (f : α → M β)
              → (λ x → subst (λ M → M β) eqM (f x)) ≡ subst (λ N → (α → N β)) eqM f
shiftFunSubst refl f = refl

shiftFunSubst' : ∀ {M M' : TyCon}
               → (eqM : M ≡ M')
               → ∀ {α β : Type}
               → (x : α)
               → (f : α → M β)
               → subst (λ M → M β) eqM (f x) ≡ subst (λ N → (α → N β)) eqM f x
shiftFunSubst' refl x f = refl
