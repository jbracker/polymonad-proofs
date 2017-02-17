
module Haskell.Parameterized.EffectMonad.Functor where

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
open import Extensionality
open import Haskell
open import Identity
open import Haskell.Functor
open import Haskell.Parameterized.EffectMonad
open import Theory.Monoid

-- -----------------------------------------------------------------------------
-- Effect Monads are Functors
-- -----------------------------------------------------------------------------

open EffectMonad hiding ( _>>=_ ; return )
open Monoid hiding ( _∙_ ; ε )

EffectMonad→Functor : ∀ {ℓ}
                → {Eff : Set ℓ}
                → {monoid : Monoid Eff}
                → (M : Eff → TyCon)
                → EffectMonad Eff {{monoid}} M 
                → ∀ (e : Eff) → Functor (M e)
EffectMonad→Functor {Eff = Eff} {monoid = monoid} M monad m = record 
  { fmap = fmap
  ; lawId = lawId
  ; lawCompose = lawCompose
  } where
    _∙_ = Monoid._∙_ monoid
    ε = Monoid.ε monoid

    monLawIdR : (m : Eff) → m ∙ ε ≡ m
    monLawIdR m = Monoid.right-id monoid {m}
    
    monLawIdL : (m : Eff) → ε ∙ m ≡ m
    monLawIdL m = Monoid.left-id monoid {m}
    
    monLawAssoc : (m n o : Eff) → m ∙ (n ∙ o) ≡ (m ∙ n) ∙ o
    monLawAssoc m n o = Monoid.assoc monoid {m} {n} {o}
    
    _>>=_ = EffectMonad._>>=_ monad
    return = EffectMonad.return monad
    
    fmap : ∀ {α β : Type} → (α → β) → M m α → M m β
    fmap {α = α} {β = β} f ma = subst₂ M (monLawIdR m) refl (ma >>= (return ∘ f))
    
    lawId : ∀ {α : Type} → fmap {α = α} identity ≡ identity
    lawId {α = α} = fun-ext (λ ma → begin
      fmap identity ma 
        ≡⟨ refl ⟩
      subst₂ M (monLawIdR m) refl (ma >>= (return ∘ identity))
        ≡⟨ cong (λ X → subst₂ M (monLawIdR m) refl X) (EffectMonad.lawIdR monad ma) ⟩
      subst₂ M (monLawIdR m) refl (subst₂ M (sym (monLawIdR m)) refl ma)
        ≡⟨ subst₂²≡id1 (Monoid.right-id monoid {m}) refl M ma ⟩
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
    
    lawCompose : ∀ {α β γ : Type} 
               → (f : β → γ) → (g : α → β) 
               → fmap (f ∘ g) ≡ fmap f ∘ fmap g
    lawCompose {β = β} {γ = γ} f g = fun-ext (λ ma → begin
      fmap (f ∘ g) ma 
        ≡⟨ refl ⟩
      subst₂ M (monLawIdR m) refl (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ subst₂ToSubst (monLawIdR m) (ma >>= (return ∘ (f ∘ g))) ⟩
      subst (λ X → M X γ) (monLawIdR m) (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ cong (λ X → subst (λ X → M X γ) X (ma >>= (return ∘ (f ∘ g)))) 
                (proof-irrelevance (monLawIdR m) 
                                   (trans (cong (λ X → m ∙ X) (sym (monLawIdL ε))) 
                                          (trans (monLawAssoc m ε ε)
                                                 (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → m ∙ X) (sym (monLawIdL ε))) 
                                              (trans (monLawAssoc m ε ε)
                                                     (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))))
            (ma >>= (return ∘ (f ∘ g)))
        ≡⟨ sym (substTrans (cong (λ X → m ∙ X) (sym (monLawIdL ε))) 
                           (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))) 
                           (λ X → M X γ) (ma >>= (return ∘ (f ∘ g)))) ⟩
      subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)))
            (subst (λ X → M X γ) (cong (λ X → m ∙ X) (sym (monLawIdL ε))) (ma >>= (return ∘ (f ∘ g))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))) X) 
                (bindFunSubstShift (sym (monLawIdL ε)) ma (return ∘ (f ∘ g))) ⟩
      subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)))
            (ma >>= (λ a → subst (λ X → M X γ) (sym (monLawIdL ε)) (return (f (g a)))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))) (ma >>= X))
                (fun-ext (λ a → sym (subst₂ToSubst (sym (monLawIdL ε)) (return (f (g a)))))) ⟩
      subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)))
            (ma >>= (λ a → subst₂ M (sym (monLawIdL ε)) refl (return (f (g a)))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m))) (ma >>= X)) 
                (fun-ext (λ a → sym (EffectMonad.lawIdL monad (g a) (return ∘ f)))) ⟩
      subst (λ X → M X γ) (trans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)))
            (ma >>= (λ a → return (g a) >>= (return ∘ f)))
        ≡⟨ sym (substTrans (monLawAssoc m ε ε) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) 
                           (λ X → M X γ) 
                           (ma >>= (λ a → return (g a) >>= (return ∘ f)))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) 
            (subst (λ X → M X γ) (monLawAssoc m ε ε) (ma >>= (λ a → return (g a) >>= (return ∘ f))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) X) 
                (sym (subst₂ToSubst (monLawAssoc m ε ε) (ma >>= (λ a → return (g a) >>= (return ∘ f))))) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) 
            (subst₂ M (monLawAssoc m ε ε) refl (ma >>= (λ a → return (g a) >>= (return ∘ f))))
        ≡⟨ cong (λ X → subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) X) 
                (EffectMonad.symLawAssoc monad ma (return ∘ g) (return ∘ f)) ⟩
      subst (λ X → M X γ) (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) 
            ((ma >>= (return ∘ g)) >>= (return ∘ f))
        ≡⟨ assocSubstShift (trans (cong (λ X → X ∙ ε) (monLawIdR m)) (monLawIdR m)) 
                           (monLawIdR m) (monLawIdR m) (ma >>= (return ∘ g)) (return ∘ f) ⟩
      subst (λ X → M X γ) (monLawIdR m) ((subst (λ X → M X β) (monLawIdR m) (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ sym (subst₂ToSubst (monLawIdR m) ((subst (λ X → M X β) (monLawIdR m) (ma >>= (return ∘ g))) >>= (return ∘ f))) ⟩
      subst₂ M (monLawIdR m) refl ((subst (λ X → M X β) (monLawIdR m) (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ cong (λ Y → subst₂ M (monLawIdR m) refl (Y >>= (return ∘ f))) (sym (subst₂ToSubst (monLawIdR m) (ma >>= (return ∘ g)))) ⟩
      subst₂ M (monLawIdR m) refl ((subst₂ M (monLawIdR m) refl (ma >>= (return ∘ g))) >>= (return ∘ f))
        ≡⟨ refl ⟩
      (fmap f ∘ fmap g) ma ∎)
