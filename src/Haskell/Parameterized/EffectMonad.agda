 
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
open import Haskell.Functor hiding ( functor )
open import Identity
open import Theory.Monoid

-- TODO: This is still unfinished work, since the constraints that can be applied to the monoid
-- elements are not modelled at all right now.


record EffectMonad {n} {Effect : Set n} (monoid : Monoid Effect) (M : Effect → TyCon) : Set (lsuc n) where
  open Monoid monoid
  field
    _>>=_ : ∀ {α β : Type} {i j : Effect} → M i α → (α → M j β) → M (i ∙ j) β
    return : ∀ {α : Type} → α → M ε α
    
    functor : (i : Effect) → Functor (M i)
    
    law-left-id : ∀ {α β : Type} {i : Effect}
           → (a : α) → (k : α → M i β) 
           → return a >>= k ≅ k a
    law-right-id : ∀ {α : Type} {i : Effect}
           → (m : M i α)
           → m >>= return ≅ m
    law-assoc : ∀ {α β γ : Type} {i j k : Effect}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≅ (m >>= f) >>= g
    
    law-monad-fmap : {α β : Type} {i : Effect} → (f : α → β) → (ma : M i α) 
                   → ma >>= (return ∘ f) ≅ Functor.fmap (functor i) f ma
  
  _>>_ : ∀ {α β : Type} {i j : Effect} → M i α → M j β → M (i ∙ j) β
  ma >> mb = ma >>= λ a → mb
  
  private
    helper : {α : Type} {i j : Effect} 
           → (ma : M i α) → (mb : M j α) → (eq : j ≡ i) → (eqM : ma ≅ mb)
           → ma ≡ subst₂ M eq refl mb
    helper ma .ma refl hrefl = refl

  law-left-id' : ∀ {α β : Type} {i : Effect}
               → (a : α) → (k : α → M i β) 
               → return a >>= k ≡ subst₂ M (sym (left-id {m = i})) refl (k a)
  law-left-id' {i = i} a k = helper (return a >>= k) (k a) (sym left-id) (law-left-id a k)
  
  law-right-id' : ∀ {α : Type} {i : Effect}
                → (m : M i α)
                → m >>= return ≡ subst₂ M (sym (right-id {m = i})) refl m
  law-right-id' {i = i} m = helper (m >>= return) m (sym right-id) (law-right-id m)

  law-assoc' : ∀ {α β γ : Type} {i j k : Effect}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≡ subst₂ M (sym $ assoc {m = i} {j} {k}) refl ((m >>= f) >>= g)
  law-assoc' {i = i} {j} {k} m f g = helper (m >>= (λ x → f x >>= g)) ((m >>= f) >>= g) (sym $ assoc {m = i} {j} {k}) (law-assoc m f g)

  law-assoc'' : ∀ {α β γ : Type} {i j k : Effect}
              → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
              → subst₂ M (assoc {m = i} {j} {k}) refl (m >>= (λ x → f x >>= g)) ≡ (m >>= f) >>= g
  law-assoc'' {α} {β} {γ} {i} {j} {k} m f g = sym $ helper ((m >>= f) >>= g) ((m >>= (λ x → f x >>= g))) assoc (hsym (law-assoc m f g))

  law-monad-fmap' : {α β : Type} {i : Effect} → (f : α → β) → (ma : M i α) 
                  → ma >>= (return ∘ f) ≡ subst₂ M (sym right-id) refl (Functor.fmap (functor i) f ma)
  law-monad-fmap' {α} {β} {i} f ma = helper (ma >>= (return ∘ f)) (Functor.fmap (functor i) f ma) (sym right-id) (law-monad-fmap f ma)

open Monoid

data EffMonadTyCons {n} (Effect : Set n) : Set n where
  EffMonadTC : Effect → EffMonadTyCons Effect

data EffMonadBinds {n} {Effect : Set n} (mon : Monoid Effect) : (M N P : IdTyCons ⊎ EffMonadTyCons Effect) → Set n where
  MonadB   : ∀ {i j} → EffMonadBinds mon (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC j)) (inj₂ (EffMonadTC (_∙_ mon i j)))
  FunctorB : ∀ {i} → EffMonadBinds mon (inj₂ (EffMonadTC i)) idTC (inj₂ (EffMonadTC i))
  ApplyB   : ∀ {i} → EffMonadBinds mon idTC (inj₂ (EffMonadTC i)) (inj₂ (EffMonadTC i))
  ReturnB  : EffMonadBinds mon idTC idTC (inj₂ (EffMonadTC (ε mon))) 

open EffectMonad renaming (_>>=_ to mBind; return to mReturn; law-assoc to mLawAssoc)

bindMonad : ∀ {n} {Effect : Set n} {M : Effect → TyCon} {i j : Effect} {mon : Monoid Effect} → (m : EffectMonad mon M)
          → [ M i , M j ]▷ M (_∙_ mon i j)
bindMonad {mon = mon} m = mBind m

bindFunctor : ∀ {n} {Effect : Set n}  {M : Effect → TyCon} {i : Effect} {mon : Monoid Effect} → (m : EffectMonad mon M)
            → [ M i , Identity ]▷ M i
bindFunctor {M = M} {i = i} {mon = mon} m ma f = subst₂ M (right-id mon {m = i}) refl (mBind m ma (λ a → mReturn m (f a)))

bindApply : ∀ {n} {Effect : Set n}  {M : Effect → TyCon} {i : Effect} {mon : Monoid Effect} → (m : EffectMonad mon M)
          → [ Identity , M i ]▷ M i
bindApply {M = M} {i = i} {mon = mon} m ma f = subst₂ M (left-id mon {m = i}) refl (mBind m (mReturn m ma) f)

bindReturn : ∀ {n} {Effect : Set n} {M : Effect → TyCon} {mon : Monoid Effect} → (m : EffectMonad mon M)
           → [ Identity , Identity ]▷ M (ε mon)
bindReturn {mon = mon} m ma f = mReturn m (f ma)
