
open import Level
open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )

open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
  renaming ( sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ ; proof-irrelevance to het-proof-irr )

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )
open import Haskell.Parameterized.Graded.Applicative

open import Theory.Monoid

module Haskell.Parameterized.Graded.Applicative.Equality where

open Monoid

abstract
  graded-applicative-eq
    : {ℓ : Level}
    → {M : Set ℓ}
    → {mon : Monoid M}
    → {F : M → TyCon}
    → {pure₀ : {α : Type} → α → F (ε mon) α}
    → {pure₁ : {α : Type} → α → F (ε mon) α}
    → {_<*>₀_ : {i j : M} {α β : Type} → F i (α → β) → F j α → F (_∙_ mon i j) β}
    → {_<*>₁_ : {i j : M} {α β : Type} → F i (α → β) → F j α → F (_∙_ mon i j) β}
    → {functor₀ : (i : M) → Functor (F i)}
    → {functor₁ : (i : M) → Functor (F i)}
    → {law-id₀ : {i : M} {α : Type} → (v : F i α) → pure₀ (λ x → x) <*>₀ v ≅ v}
    → {law-id₁ : {i : M} {α : Type} → (v : F i α) → pure₁ (λ x → x) <*>₁ v ≅ v}
    → {law-composition₀ : {i j k : M} {α β γ : Type} → (u : F i (β → γ)) → (v : F j (α → β)) → (w : F k α) → (((pure₀ _∘_) <*>₀ u) <*>₀ v) <*>₀ w ≅ u <*>₀ (v <*>₀ w)}
    → {law-composition₁ : {i j k : M} {α β γ : Type} → (u : F i (β → γ)) → (v : F j (α → β)) → (w : F k α) → (((pure₁ _∘_) <*>₁ u) <*>₁ v) <*>₁ w ≅ u <*>₁ (v <*>₁ w)}
    → {law-homomorphism₀ : {α β : Type} → (x : α) → (f : α → β) → pure₀ f <*>₀ pure₀ x ≅ pure₀ (f x)}
    → {law-homomorphism₁ : {α β : Type} → (x : α) → (f : α → β) → pure₁ f <*>₁ pure₁ x ≅ pure₁ (f x)}
    → {law-interchange₀ : {i : M} {α β : Type} → (u : F i (α → β)) → (x : α) → u <*>₀ pure₀ x ≅ pure₀ (λ f → f x) <*>₀ u}
    → {law-interchange₁ : {i : M} {α β : Type} → (u : F i (α → β)) → (x : α) → u <*>₁ pure₁ x ≅ pure₁ (λ f → f x) <*>₁ u}
    → {law-applicative-fmap₀ : {i : M} {α β : Type} → (f : α → β) → (x : F i α) → (Functor.fmap (functor₀ i)) f x ≅ pure₀ f <*>₀ x}
    → {law-applicative-fmap₁ : {i : M} {α β : Type} → (f : α → β) → (x : F i α) → (Functor.fmap (functor₁ i)) f x ≅ pure₁ f <*>₁ x}
    → (λ {α} → pure₀ {α}) ≡ pure₁
    → (λ {i j} {α β} → _<*>₀_ {i} {j} {α} {β}) ≡ _<*>₁_
    → (λ i → functor₀ i) ≡ functor₁
    → graded-applicative {monoid = mon} {F = F} pure₀ _<*>₀_ functor₀ law-id₀ law-composition₀ law-homomorphism₀ law-interchange₀ law-applicative-fmap₀
    ≡ graded-applicative {monoid = mon} {F = F} pure₁ _<*>₁_ functor₁ law-id₁ law-composition₁ law-homomorphism₁ law-interchange₁ law-applicative-fmap₁
  graded-applicative-eq {ℓ} {M} {mon} {F} {p} {.p} {ap} {.ap} {f} {.f} {li₀} {li₁} {co₀} {co₁} {hom₀} {hom₁} {in₀} {in₁} {af₀} {af₁} refl refl refl
    = cong₅ (graded-applicative p ap f) p1 p2 p3 p4 p5
    where
      abstract
        p1 : (λ {i} {α} → li₀ {i} {α}) ≡ li₁
        p1 = implicit-fun-ext
           $ λ i → implicit-fun-ext
           $ λ α → fun-ext
           $ λ v → het-proof-irr (li₀ {i} {α} v) (li₁ {i} {α} v)
        
      abstract
        p2 : (λ {i j k} {α β γ} → co₀ {i} {j} {k} {α} {β} {γ}) ≡ co₁
        p2 = implicit-fun-ext
           $ λ i → implicit-fun-ext
           $ λ j → implicit-fun-ext
           $ λ k → implicit-fun-ext
           $ λ α → implicit-fun-ext
           $ λ β → implicit-fun-ext
           $ λ γ → fun-ext
           $ λ f → fun-ext
           $ λ g → fun-ext
           $ λ a → het-proof-irr (co₀ {i} {j} {k} {α} {β} {γ} f g a) (co₁ f g a)
      
      abstract
        p3 : (λ {α β} → hom₀ {α} {β}) ≡ hom₁
        p3 = implicit-fun-ext
           $ λ α → implicit-fun-ext
           $ λ β → fun-ext
           $ λ a → fun-ext
           $ λ f → het-proof-irr (hom₀ {α} {β} a f) (hom₁ a f)
      
      abstract
        p4 : (λ {i} {α β} → in₀ {i} {α} {β}) ≡ in₁
        p4 = implicit-fun-ext
           $ λ i → implicit-fun-ext
           $ λ α → implicit-fun-ext
           $ λ β → fun-ext
           $ λ f → fun-ext
           $ λ a → het-proof-irr (in₀ {i} {α} {β} f a) (in₁ f a)
      
      abstract
        p5 : (λ {i} {α β} → af₀ {i} {α} {β}) ≡ af₁
        p5 = implicit-fun-ext
           $ λ i → implicit-fun-ext
           $ λ α → implicit-fun-ext
           $ λ β → fun-ext
           $ λ f → fun-ext
           $ λ a → het-proof-irr (af₀ {i} {α} {β} f a) (af₁ f a)

