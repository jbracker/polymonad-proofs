 
module Haskell.Parameterized.Graded.Monad where

-- Stdlib
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ( proof-irrelevance )
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ ; subst to hsubst )
open ≡-Reasoning

-- Local
open import Utilities
open import Congruence
open import Extensionality
open import Haskell
open import Haskell.Functor hiding ( functor )
open import Identity
open import Theory.Monoid

-- TODO: This is still unfinished work, since the constraints that can be applied to the monoid
-- elements are not modelled at all right now.


record GradedMonad {ℓ} {Eff : Set ℓ} (monoid : Monoid Eff) (M : Eff → TyCon) : Set (lsuc ℓ) where
  constructor graded-monad
  open Monoid monoid
  field
    _>>=_ : {α β : Type} {i j : Eff} → M i α → (α → M j β) → M (i ∙ j) β
    return : {α : Type} → α → M ε α
    
    functor : (i : Eff) → Functor (M i)
    
    law-left-id : {α β : Type} {i : Eff}
                → (a : α) → (k : α → M i β) 
                → return a >>= k ≅ k a
    law-right-id : {α : Type} {i : Eff}
                 → (m : M i α)
                 → m >>= return ≅ m
    law-assoc : {α β γ : Type} {i j k : Eff}
              → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
              → m >>= (λ x → f x >>= g) ≅ (m >>= f) >>= g
    
    law-monad-fmap : {α β : Type} {i : Eff} → (f : α → β) → (ma : M i α) 
                   → ma >>= (return ∘ f) ≅ Functor.fmap (functor i) f ma
  
  _>>_ : ∀ {α β : Type} {i j : Eff} → M i α → M j β → M (i ∙ j) β
  ma >> mb = ma >>= λ a → mb
  
  Mi≅Miε : {α : Type} {i : Eff} → M i α ≅ M (i ∙ ε) α
  Mi≅Miε {α} {i} = hcong (λ X → M X α) (≡-to-≅ (sym right-id))
  
  Mi≅Mεi : {α : Type} {i : Eff} → M i α ≅ M (ε ∙ i) α
  Mi≅Mεi {α} {i} = hcong (λ X → M X α) (≡-to-≅ (sym left-id))
  
  bind = _>>=_
  
  join : {α : Type} {i j : Eff} → M i (M j α) → M (i ∙ j) α
  join mma = mma >>= λ x → x

  fmap : {α β : Type} {i : Eff} → (α → β) → M i α → M i β
  fmap {i = i} f ma = Functor.fmap (functor i) f ma
  
  bind-arg₁ : {α β : Type} {i j k : Eff} → i ≡ j → (ma : M i α) → (mb : M j α) → ma ≅ mb → (f : α → M k β) → ma >>= f ≅ mb >>= f
  bind-arg₁ refl ma .ma hrefl f = hrefl

  bind-arg₂ : {α β : Type} {i j k : Eff} → j ≡ k → (ma : M i α) → (f : α → M j β) → (g : α → M k β) → f ≅ g → ma >>= f ≅ ma >>= g
  bind-arg₂ refl ma f .f hrefl = hrefl
  
  private
    helper : {α : Type} {i j : Eff} 
           → (ma : M i α) → (mb : M j α) → (eq : j ≡ i) → (eqM : ma ≅ mb)
           → ma ≡ subst₂ M eq refl mb
    helper ma .ma refl hrefl = refl

  law-left-id' : ∀ {α β : Type} {i : Eff}
               → (a : α) → (k : α → M i β) 
               → return a >>= k ≡ subst₂ M (sym (left-id {m = i})) refl (k a)
  law-left-id' {i = i} a k = helper (return a >>= k) (k a) (sym left-id) (law-left-id a k)
  
  law-right-id' : ∀ {α : Type} {i : Eff}
                → (m : M i α)
                → m >>= return ≡ subst₂ M (sym (right-id {m = i})) refl m
  law-right-id' {i = i} m = helper (m >>= return) m (sym right-id) (law-right-id m)

  law-assoc' : ∀ {α β γ : Type} {i j k : Eff}
             → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
             → m >>= (λ x → f x >>= g) ≡ subst₂ M (sym $ assoc {m = i} {j} {k}) refl ((m >>= f) >>= g)
  law-assoc' {i = i} {j} {k} m f g = helper (m >>= (λ x → f x >>= g)) ((m >>= f) >>= g) (sym $ assoc {m = i} {j} {k}) (law-assoc m f g)

  law-assoc'' : ∀ {α β γ : Type} {i j k : Eff}
              → (m : M i α) → (f : α → M j β) → (g : β → M k γ)
              → subst₂ M (assoc {m = i} {j} {k}) refl (m >>= (λ x → f x >>= g)) ≡ (m >>= f) >>= g
  law-assoc'' {α} {β} {γ} {i} {j} {k} m f g = sym $ helper ((m >>= f) >>= g) ((m >>= (λ x → f x >>= g))) assoc (hsym (law-assoc m f g))

  law-monad-fmap' : {α β : Type} {i : Eff} → (f : α → β) → (ma : M i α) 
                  → ma >>= (return ∘ f) ≡ subst₂ M (sym right-id) refl (Functor.fmap (functor i) f ma)
  law-monad-fmap' {α} {β} {i} f ma = helper (ma >>= (return ∘ f)) (Functor.fmap (functor i) f ma) (sym right-id) (law-monad-fmap f ma)


open Monoid

graded-monad-eq : {ℓ : Level}
  → {Eff : Set ℓ} 
  → {mon : Monoid Eff}
  → {M : Eff → TyCon}
  → {_>>=₀_ : {α β : Type} {i j : Eff} → M i α → (α → M j β) → M (_∙_ mon i j) β}
  → {_>>=₁_ : {α β : Type} {i j : Eff} → M i α → (α → M j β) → M (_∙_ mon i j) β}
  → {return₀ : {α : Type} → α → M (ε mon) α}
  → {return₁ : {α : Type} → α → M (ε mon) α}
  → {functor₀ : (i : Eff) → Functor (M i)}
  → {functor₁ : (i : Eff) → Functor (M i)}
  → {law-right-id₀ : {α : Type} {i : Eff} → (m : M i α) → m >>=₀ return₀ ≅ m}
  → {law-right-id₁ : {α : Type} {i : Eff} → (m : M i α) → m >>=₁ return₁ ≅ m}
  → {law-left-id₀ : {α β : Type} {i : Eff} → (a : α) → (k : α → M i β) → return₀ a >>=₀ k ≅ k a}
  → {law-left-id₁ : {α β : Type} {i : Eff} → (a : α) → (k : α → M i β) → return₁ a >>=₁ k ≅ k a}
  → {law-assoc₀ : {α β γ : Type} {i j k : Eff} → (m : M i α) → (f : α → M j β) → (g : β → M k γ) → m >>=₀ (λ x → f x >>=₀ g) ≅ (m >>=₀ f) >>=₀ g}
  → {law-assoc₁ : {α β γ : Type} {i j k : Eff} → (m : M i α) → (f : α → M j β) → (g : β → M k γ) → m >>=₁ (λ x → f x >>=₁ g) ≅ (m >>=₁ f) >>=₁ g}
  → {law-monad-fmap₀ : {α β : Type} {i : Eff} → (f : α → β) → (ma : M i α) → ma >>=₀ (return₀ ∘ f) ≅ Functor.fmap (functor₀ i) f ma}
  → {law-monad-fmap₁ : {α β : Type} {i : Eff} → (f : α → β) → (ma : M i α) → ma >>=₁ (return₁ ∘ f) ≅ Functor.fmap (functor₁ i) f ma}
  → (λ {a} {b} {i} {j} → _>>=₀_ {a} {b} {i} {j}) ≡ _>>=₁_
  → (λ {a} → return₀ {a}) ≡ return₁
  → functor₀ ≡ functor₁
  → graded-monad {ℓ = ℓ} {Eff = Eff} {monoid = mon} {M = M} _>>=₀_ return₀ functor₀ law-left-id₀ law-right-id₀ law-assoc₀ law-monad-fmap₀ 
  ≡ graded-monad _>>=₁_ return₁ functor₁ law-left-id₁ law-right-id₁ law-assoc₁ law-monad-fmap₁
graded-monad-eq {ℓ} {Eff} {mon} {M} {_>>=_} {._} {return} {._} {functor} {._} {ri₀} {ri₁} {li₀} {li₁} {as₀} {as₁} {mf₀} {mf₁} refl refl refl = cong₄ (graded-monad _>>=_ return functor) p1 p2 p3 p4
  where 
    p1 : (λ {a} {b} {i} → li₀ {a} {b} {i}) ≡ li₁
    p1 = implicit-fun-ext 
       $ λ α → implicit-fun-ext 
       $ λ β → implicit-fun-ext 
       $ λ i → fun-ext 
       $ λ a → fun-ext 
       $ λ k → proof-irrelevance (li₀ {α} {β} {i} a k) (li₁ {α} {β} {i} a k)
    
    p2 : (λ {a} {i} → ri₀ {a} {i}) ≡ ri₁
    p2 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ i → fun-ext 
       $ λ m → proof-irrelevance (ri₀ {a} {i} m) (ri₁ {a} {i} m)
    
    p3 : (λ {a} {b} {c} {i} {j} {k} → as₀ {a} {b} {c} {i} {j} {k}) ≡ as₁
    p3 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ c → implicit-fun-ext 
       $ λ i → implicit-fun-ext 
       $ λ j → implicit-fun-ext 
       $ λ k → fun-ext 
       $ λ m → fun-ext 
       $ λ f → fun-ext 
       $ λ g → proof-irrelevance (as₀ {a} {b} {c} {i} {j} {k} m f g) (as₁ {a} {b} {c} {i} {j} {k} m f g)
    
    p4 : (λ {a} {b} {i} → mf₀ {a} {b} {i}) ≡ mf₁
    p4 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ i → fun-ext 
       $ λ f → fun-ext 
       $ λ m → proof-irrelevance (mf₀ {a} {b} {i} f m) (mf₁ {a} {b} {i} f m)

data GradedMonadTyCons {n} (Eff : Set n) : Set n where
  GradedMonadTC : Eff → GradedMonadTyCons Eff

data GradedMonadBinds {n} {Eff : Set n} (mon : Monoid Eff) : (M N P : IdTyCons ⊎ GradedMonadTyCons Eff) → Set n where
  MonadB   : ∀ {i j} → GradedMonadBinds mon (inj₂ (GradedMonadTC i)) (inj₂ (GradedMonadTC j)) (inj₂ (GradedMonadTC (_∙_ mon i j)))
  FunctorB : ∀ {i} → GradedMonadBinds mon (inj₂ (GradedMonadTC i)) idTC (inj₂ (GradedMonadTC i))
  ApplyB   : ∀ {i} → GradedMonadBinds mon idTC (inj₂ (GradedMonadTC i)) (inj₂ (GradedMonadTC i))
  ReturnB  : GradedMonadBinds mon idTC idTC (inj₂ (GradedMonadTC (ε mon))) 

open GradedMonad renaming (_>>=_ to mBind; return to mReturn; law-assoc to mLawAssoc)

bindMonad : ∀ {n} {Eff : Set n} {M : Eff → TyCon} {i j : Eff} {mon : Monoid Eff} → (m : GradedMonad mon M)
          → [ M i , M j ]▷ M (_∙_ mon i j)
bindMonad {mon = mon} m = mBind m

bindFunctor : ∀ {n} {Eff : Set n}  {M : Eff → TyCon} {i : Eff} {mon : Monoid Eff} → (m : GradedMonad mon M)
            → [ M i , Identity ]▷ M i
bindFunctor {M = M} {i = i} {mon = mon} m ma f = subst₂ M (right-id mon {m = i}) refl (mBind m ma (λ a → mReturn m (f a)))

bindApply : ∀ {n} {Eff : Set n}  {M : Eff → TyCon} {i : Eff} {mon : Monoid Eff} → (m : GradedMonad mon M)
          → [ Identity , M i ]▷ M i
bindApply {M = M} {i = i} {mon = mon} m ma f = subst₂ M (left-id mon {m = i}) refl (mBind m (mReturn m ma) f)

bindReturn : ∀ {n} {Eff : Set n} {M : Eff → TyCon} {mon : Monoid Eff} → (m : GradedMonad mon M)
           → [ Identity , Identity ]▷ M (ε mon)
bindReturn {mon = mon} m ma f = mReturn m (f ma)
