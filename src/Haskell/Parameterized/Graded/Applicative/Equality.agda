
open import Level
open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming (sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Graded.Applicative

open import Theory.Monoid

module Haskell.Parameterized.Graded.Applicative.Equality where
{-
abstract
  applicative-eq : {F : TyCon}
                 → {pure₀ : ∀ {α : Type} → α → F α}
                 → {pure₁ : ∀ {α : Type} → α → F α}
                 → {_<*>₀_ : ∀ {α β : Type} → F (α → β) → F α → F β}
                 → {_<*>₁_ : ∀ {α β : Type} → F (α → β) → F α → F β}
                 → {functor₀ : Functor F}
                 → {functor₁ : Functor F}
                 → {law-id₀ : ∀ {α : Type} → (v : F α) → pure₀ (λ x → x) <*>₀ v ≡ v}
                 → {law-id₁ : ∀ {α : Type} → (v : F α) → pure₁ (λ x → x) <*>₁ v ≡ v}
                 → {law-composition₀ : ∀ {α β γ : Type} → (u : F (β → γ)) → (v : F (α → β)) → (w : F α) → (((pure₀ _∘_) <*>₀ u) <*>₀ v) <*>₀ w ≡ u <*>₀ (v <*>₀ w)}
                 → {law-composition₁ : ∀ {α β γ : Type} → (u : F (β → γ)) → (v : F (α → β)) → (w : F α) → (((pure₁ _∘_) <*>₁ u) <*>₁ v) <*>₁ w ≡ u <*>₁ (v <*>₁ w)}
                 → {law-homomorphism₀ : ∀ {α β : Type} → (x : α) → (f : α → β) → pure₀ f <*>₀ pure₀ x ≡ pure₀ (f x)}
                 → {law-homomorphism₁ : ∀ {α β : Type} → (x : α) → (f : α → β) → pure₁ f <*>₁ pure₁ x ≡ pure₁ (f x)}
                 → {law-interchange₀ : ∀ {α β : Type} → (u : F (α → β)) → (x : α) → u <*>₀ pure₀ x ≡ pure₀ (λ f → f x) <*>₀ u}
                 → {law-interchange₁ : ∀ {α β : Type} → (u : F (α → β)) → (x : α) → u <*>₁ pure₁ x ≡ pure₁ (λ f → f x) <*>₁ u}
                 → {law-applicative-fmap₀ : ∀ {α β : Type} → (f : α → β) → (x : F α) → (Functor.fmap functor₀) f x ≡ pure₀ f <*>₀ x}
                 → {law-applicative-fmap₁ : ∀ {α β : Type} → (f : α → β) → (x : F α) → (Functor.fmap functor₁) f x ≡ pure₁ f <*>₁ x}
                 → (λ {α} → pure₀ {α}) ≡ pure₁
                 → (λ {α β} → _<*>₀_ {α} {β}) ≡ _<*>₁_
                 → functor₀ ≡ functor₁
                 → applicative {F = F} pure₀ _<*>₀_ functor₀ law-id₀ law-composition₀ law-homomorphism₀ law-interchange₀ law-applicative-fmap₀
                 ≡ applicative {F = F} pure₁ _<*>₁_ functor₁ law-id₁ law-composition₁ law-homomorphism₁ law-interchange₁ law-applicative-fmap₁
  applicative-eq {F} {p} {.p} {ap} {.ap} {f} {.f} {li₀} {li₁} {co₀} {co₁} {hom₀} {hom₁} {in₀} {in₁} {af₀} {af₁} refl refl refl
    = cong₅ (applicative p ap f) p1 p2 p3 p4 p5
    where
      abstract
        p1 : (λ {α} → li₀ {α}) ≡ li₁
        p1 = implicit-fun-ext (λ α → fun-ext (λ fa → proof-irrelevance (li₀ fa) (li₁ fa)))
      
      abstract
        p2 : (λ {α β γ} → co₀ {α} {β} {γ}) ≡ co₁
        p2 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → implicit-fun-ext (λ γ → fun-ext
           $ λ f → fun-ext (λ g → fun-ext (λ a → proof-irrelevance (co₀ f g a) (co₁ f g a))))))
      
      abstract
        p3 : (λ {α β} → hom₀ {α} {β}) ≡ hom₁
        p3 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
           $ λ a → fun-ext (λ f → proof-irrelevance (hom₀ a f) (hom₁ a f))))
      
      abstract
        p4 : (λ {α β} → in₀ {α} {β}) ≡ in₁
        p4 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
           $ λ f → fun-ext (λ a → proof-irrelevance (in₀ f a) (in₁ f a))))
      
      abstract
        p5 : (λ {α β} → af₀ {α} {β}) ≡ af₁
        p5 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
           $ λ f → fun-ext (λ a → proof-irrelevance (af₀ f a) (af₁ f a)))) 
-}
