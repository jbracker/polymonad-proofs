
module Parameterized.EffectMonad.Functor where

-- Stdlib
open import Function
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Functor
open import Parameterized.EffectMonad

-- -----------------------------------------------------------------------------
-- Effect Monads are Functors
-- -----------------------------------------------------------------------------

open EffectMonad hiding ( _>>=_ ; return )
open Parameterized.EffectMonad.Monoid

EffectMonad→Functor : ∀ {ℓ}
                → {Eff : Set ℓ}
                → {monoid : Monoid Eff}
                → (M : Eff → TyCon)
                → EffectMonad Eff {{monoid}} M 
                → ∀ (e : Eff) → Functor (M e)
EffectMonad→Functor {Eff = Eff} {monoid = monoid} M monad m = record 
  { fmap = fmap
  ; lawId = lawId
  ; lawDist = lawDist
  } where
    _∙_ = Monoid._∙_ monoid
    ε = Monoid.ε monoid
    
    _>>=_ = EffectMonad._>>=_ monad
    return = EffectMonad.return monad
    
    fmap : ∀ {α β : Type} → (α → β) → M m α → M m β
    fmap {α = α} {β = β} f ma = subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return ∘ f))
    
    lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawId {α = α} = funExt (λ ma → begin
      fmap identity ma 
        ≡⟨ refl ⟩
      subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return ∘ identity))
        ≡⟨ cong (λ X → subst₂ M (Monoid.lawIdR monoid m) refl X) (EffectMonad.lawIdR monad ma) ⟩
      subst₂ M (Monoid.lawIdR monoid m) refl (subst₂ M (sym (Monoid.lawIdR monoid m)) refl ma)
        ≡⟨ subst₂²≡id1 (Monoid.lawIdR monoid m) refl M ma ⟩
      identity ma ∎)
        
    bindFunSubstShift : {α β : Type} {m n p : Eff}
                      → (eq : n ≡ p)
                      → (ma : M m α)
                      → (f : α → M n β)
                      → subst (λ X → M X β) (cong (λ X → m ∙ X) eq) (ma >>= f)
                        ≡ ma >>= (λ a → subst (λ X → M X β) eq (f a))
    bindFunSubstShift refl ma f = refl
    
    subst₂ToSubst : {α : Type} {m n : Eff}
                  → (eq : m ≡ n)
                  → (ma : M m α)
                  → subst₂ M eq refl ma ≡ subst (λ X → M X α) eq ma 
    subst₂ToSubst refl ma = refl
    
    assocSubstShift : {α β : Type} {m n p s : Eff}
                    → (assoc : m ∙ n ≡ p)
                    → (inner : m ≡ s)
                    → (outer : s ∙ n ≡ p)
                    → (ma : M m α)
                    → (f : α → M n β)
                    → subst (λ X → M X β) assoc (ma >>= f) 
                    ≡ subst (λ X → M X β) outer ((subst (λ X → M X α) inner ma) >>= f)
    assocSubstShift refl refl refl ma f = refl
    
    lawDist : ∀ {α β γ : Type} 
            → (f : β → γ) → (g : α → β) 
            → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    lawDist {β = β} {γ = γ} f g = funExt (λ ma → begin
      fmap (f ∘ g) ma 
        ≡⟨ refl ⟩
      subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ subst₂ToSubst (Monoid.lawIdR monoid m) (ma >>= (return ∘ (f ∘ g))) ⟩
      subst (λ X → M X γ) (Monoid.lawIdR monoid m) (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ cong (λ X → subst (λ X → M X γ) X (ma >>= (return ∘ (f ∘ g)))) 
                (proof-irrelevance (Monoid.lawIdR monoid m) 
                                   (trans (cong (λ X → m ∙ X) (sym (Monoid.lawIdL monoid ε))) 
                                          (trans (sym (Monoid.lawAssoc monoid m ε ε)) 
                                                 (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → m ∙ X) (sym (Monoid.lawIdL monoid ε))) 
                                              (trans (sym (Monoid.lawAssoc monoid m ε ε)) 
                                                     (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))))
            (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ sym (substTrans (cong (λ X → m ∙ X) (sym (Monoid.lawIdL monoid ε))) 
                           (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))) 
                           (λ X → M X γ) (ma >>= (return ∘ (f ∘ g)))) ⟩
      subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)))
            (subst (λ X → M X γ) (cong (λ X → m ∙ X) (sym (Monoid.lawIdL monoid ε))) (ma >>= (return ∘ (f ∘ g))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))) X) 
                (bindFunSubstShift (sym (Monoid.lawIdL monoid ε)) ma (return ∘ (f ∘ g))) ⟩
      subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)))
            (ma >>= (λ a → subst (λ X → M X γ) (sym (Monoid.lawIdL monoid ε)) (return (f (g a)))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))) (ma >>= X))
                (funExt (λ a → sym (subst₂ToSubst (sym (Monoid.lawIdL monoid ε)) (return (f (g a)))))) ⟩
      subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)))
            (ma >>= (λ a → subst₂ M (sym (Monoid.lawIdL monoid ε)) refl (return (f (g a)))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m))) (ma >>= X)) 
                (funExt (λ a → sym (EffectMonad.lawIdL monad (g a) (return ∘ f)))) ⟩
      subst (λ X → M X γ) (trans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)))
            (ma >>= (λ a → return (g a) >>= (return ∘ f)))
        ≡⟨ sym (substTrans (sym (Monoid.lawAssoc monoid m ε ε)) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) 
                           (λ X → M X γ) 
                           (ma >>= (λ a → return (g a) >>= (return ∘ f)))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) 
            (subst (λ X → M X γ) (sym (Monoid.lawAssoc monoid m ε ε)) (ma >>= (λ a → return (g a) >>= (return ∘ f))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) X) 
                (sym (subst₂ToSubst (sym (Monoid.lawAssoc monoid m ε ε)) (ma >>= (λ a → return (g a) >>= (return ∘ f))))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) 
            (subst₂ M (sym (Monoid.lawAssoc monoid m ε ε)) refl (ma >>= (λ a → return (g a) >>= (return ∘ f))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) X) 
                (EffectMonad.symLawAssoc monad ma (return ∘ g) (return ∘ f)) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) 
            ((ma >>= (return ∘ g)) >>= (return ∘ f))
        ≡⟨ assocSubstShift (trans (cong (λ X → X ∙ ε) (Monoid.lawIdR monoid m)) (Monoid.lawIdR monoid m)) 
                           (Monoid.lawIdR monoid m) (Monoid.lawIdR monoid m) (ma >>= (return ∘ g)) (return ∘ f) ⟩
      subst (λ X → M X γ) (Monoid.lawIdR monoid m) ((subst (λ X → M X β) (Monoid.lawIdR monoid m) (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ sym (subst₂ToSubst (Monoid.lawIdR monoid m) ((subst (λ X → M X β) (Monoid.lawIdR monoid m) (ma >>= (return ∘ g))) >>= (return ∘ f))) ⟩
      subst₂ M (Monoid.lawIdR monoid m) refl ((subst (λ X → M X β) (Monoid.lawIdR monoid m) (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ cong (λ Y → subst₂ M (Monoid.lawIdR monoid m) refl (Y >>= (return ∘ f))) (sym (subst₂ToSubst (Monoid.lawIdR monoid m) (ma >>= (return ∘ g)))) ⟩
      subst₂ M (Monoid.lawIdR monoid m) refl ((subst₂ M (Monoid.lawIdR monoid m) refl (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ refl ⟩
      (fmap f ∘ fmap g) ma ∎)
