 
module Haskell.Parameterized.EffectMonad where

-- Stdlib
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ )
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Theory.Monoid

-- TODO: This is still unfinished work, since the constraints that can be applied to the monoid
-- elements are not modelled at all right now.

open Monoid {{...}} renaming ( assoc to monLawAssoc ; carrier to monCarrier )
--open Monoid

record EffectMonad {n} (Effect : Set n) {{effectMonoid : Monoid Effect}} (M : Effect → TyCon) : Set (lsuc n) where
  field
    _>>=_ : ∀ {α β : Type} {i j : Effect} → M i α → (α → M j β) → M (i ∙ j) β
    return : ∀ {α : Type} → α → M ε α
    
    law-left-id : ∀ {α β : Type} {i : Effect}
           → (a : α) → (k : α → M i β) 
           → return a >>= k ≡ subst₂ M (sym (left-id {m = i})) refl (k a)
    law-right-id : ∀ {α : Type} {i : Effect}
           → (m : M i α)
           → m >>= return ≡ subst₂ M (sym (right-id {m = i})) refl m
    law-assoc : ∀ {α β γ : Type} {i j k : Effect}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≡ subst₂ M (sym $ monLawAssoc {m = i} {j} {k}) refl ((m >>= f) >>= g)
  
  _>>_ : ∀ {α β : Type} {i j : Effect} → M i α → M j β → M (i ∙ j) β
  ma >> mb = ma >>= λ a → mb

  symLawAssoc : ∀ {α β γ : Type} {i j k : Effect}
              → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
              → subst₂ M (monLawAssoc {m = i} {j} {k}) refl (m >>= (λ x → f x >>= g)) ≡ (m >>= f) >>= g
  symLawAssoc {α} {β} {γ} {i} {j} {k} m f g = begin
    subst₂ M (monLawAssoc {m = i} {j} {k}) refl (m >>= (λ x → f x >>= g))
      ≡⟨ cong (λ X → subst₂ M (monLawAssoc {m = i} {j} {k}) refl X) (law-assoc m f g) ⟩
    subst₂ M (monLawAssoc {m = i} {j} {k}) refl (subst₂ M (sym $ monLawAssoc {m = i} {j} {k}) refl ((m >>= f) >>= g))
      ≡⟨ subst₂²≡id1 (monLawAssoc {m = i} {j} {k}) refl M ((m >>= f) >>= g) ⟩
    (m >>= f) >>= g ∎
  
  private
    helper : {α : Type} {i j : Effect} → (eq : i ≡ j) → (ma : M i α) → subst₂ M eq refl ma ≅ ma
    helper refl ma = hrefl
  
  het-left-id : ∀ {α β : Type} {i : Effect} → (a : α) → (k : α → M i β) → return a >>= k ≅ k a
  het-left-id {α} {β} {i} a k = htrans (≡-to-≅ (law-left-id a k)) (helper (sym $ left-id {m = i}) (k a))

  het-right-id : ∀ {α : Type} {i : Effect} → (m : M i α) → m >>= return ≅ m
  het-right-id {α} {i} m = htrans (≡-to-≅ (law-right-id m)) (helper (sym $ right-id {m = i}) m)

  het-assoc : ∀ {α β γ : Type} {i j k : Effect} → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
            → m >>= (λ x → f x >>= g) ≅ (m >>= f) >>= g
  het-assoc {α} {β} {γ} {i} {j} {k} m f g = htrans (≡-to-≅ (law-assoc m f g)) (helper (sym $ monLawAssoc {m = i} {j} {k}) ((m >>= f) >>= g))

data EffMonadTyCons {n} (Effect : Set n) : Set n where
  EffMonadTC : Effect → EffMonadTyCons Effect

data EffMonadBinds {n} (Effect : Set n) {{effectMonoid : Monoid Effect}} : (M N P : IdTyCons ⊎ EffMonadTyCons Effect) → Set n where
  MonadB   : ∀ {i j} → EffMonadBinds Effect (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC (i ∙ j)))
  FunctorB : ∀ {i} → EffMonadBinds Effect (inj₂ (EffMonadTC i)) idTC (inj₂ (EffMonadTC i))
  ApplyB   : ∀ {i} → EffMonadBinds Effect idTC (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC i))
  ReturnB  : EffMonadBinds Effect idTC idTC (inj₂ (EffMonadTC ε)) 

open EffectMonad renaming (_>>=_ to mBind; return to mReturn; law-assoc to mLawAssoc)

bindMonad : ∀ {n} {Effect : Set n} {M : Effect → TyCon} {i j : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
          → [ M i , M j ]▷ M (i ∙ j)
bindMonad m = mBind m

bindFunctor : ∀ {n} {Effect : Set n}  {M : Effect → TyCon} {i : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
            → [ M i , Identity ]▷ M i
bindFunctor {M = M} {i = i} m ma f = subst₂ M (right-id {m = i}) refl (mBind m ma (λ a → mReturn m (f a)))

bindApply : ∀ {n} {Effect : Set n}  {M : Effect → TyCon} {i : Effect} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
          → [ Identity , M i ]▷ M i
bindApply {M = M} {i = i} m ma f = subst₂ M (left-id {m = i}) refl (mBind m (mReturn m ma) f)

bindReturn : ∀ {n} {Effect : Set n} {M : Effect → TyCon} {{effMonoid : Monoid Effect}} → (m : EffectMonad Effect M)
           → [ Identity , Identity ]▷ M ε
bindReturn m ma f = mReturn m (f ma)
