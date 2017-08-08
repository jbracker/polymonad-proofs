
open import Level
open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming (sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Haskell 
open import Haskell.Functor hiding ( functor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Graded.Applicative
open import Haskell.Parameterized.Graded.Monad

open import Theory.Monoid

open import Extensionality

module Haskell.Parameterized.Graded.Applicative.FromGradedMonad where 

GradedMonad→GradedApplicative : {ℓ : Level} {Eff : Set ℓ} {mon : Monoid Eff} {M : Eff → TyCon}
                              → GradedMonad mon M
                              → GradedApplicative mon M
GradedMonad→GradedApplicative {ℓ} {Eff} {mon} {M} monad
  = graded-applicative pure _<*>_ functor law-identity law-composition law-homomorphism law-interchange law-applicative-fmap
  where
    open GradedMonad monad
    open Monoid mon

    pure : {α : Type} → α → M (Monoid.ε mon) α
    pure = return

    _<*>_ : {i j : Eff} {α β : Type} → M i (α → β) → M j α → M (i ∙ j) β
    mf <*> ma = mf >>= (λ f → fmap f ma)

    law-applicative-fmap : {i : Eff} {α β : Type} → (f : α → β) (ma : M i α)
                         → fmap f ma ≅ (pure f <*> ma)
    law-applicative-fmap {i} {α} {β} f ma = begin
      (M i β ∋ fmap f ma)
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ (sym left-id)) (hsym $ law-left-id f (λ f → fmap f ma)) ⟩
      (M (ε ∙ i) β ∋ (return f >>= (λ f → fmap f ma)))
        ≡⟨⟩
      (M (ε ∙ i) β ∋ (pure f <*> ma)) ∎
    
    law-identity : {i : Eff} {α : Type} → (v : M i α)
                 → (pure (λ x → x) <*> v) ≅ v
    law-identity {i} {α} v = begin
      (M (ε ∙ i) α ∋ (pure (λ x → x) <*> v))
        ≡⟨⟩
      (M (ε ∙ i) α ∋ (return (λ x → x) >>= (λ f → fmap f v)))
        ≅⟨ hcong₂ (λ X Y → M X α ∋ Y) (≡-to-≅ left-id) (law-left-id (λ x → x) (λ f → fmap f v)) ⟩
      (M i α ∋ (fmap (λ x → x) v))
        ≅⟨ ≡-to-≅ (cong (λ X → X v) (Functor.law-id (functor i))) ⟩
      (M i α ∋ v) ∎

    law-composition : {i j k : Eff} {α β γ : Type}
                    → (u : M i (β → γ)) (v : M j (α → β)) (w : M k α)
                    → (((pure _∘_ <*> u) <*> v) <*> w) ≅ (u <*> (v <*> w))
    law-composition {i} {j} {k} {α} {β} {γ} u v w = {!!}

    law-homomorphism : {α β : Type} → (x : α) (f : α → β)
                     → (pure f <*> pure x) ≅ pure (f x)
    law-homomorphism {α} {β} x f = begin
      (M (ε ∙ ε) β ∋ (pure f <*> pure x))
        ≡⟨⟩
      (M (ε ∙ ε) β ∋ (return f >>= (λ g → fmap g (return x))))
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ left-id) (law-left-id f (λ g → fmap g (return x))) ⟩
      (M ε β ∋ (fmap f (return x)))
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ (sym left-id)) (hsym (law-monad-fmap f (return x))) ⟩
      (M (ε ∙ ε) β ∋ (return x >>= (return ∘ f)))
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ left-id) (law-left-id x (return ∘ f)) ⟩
      (M ε β ∋ return (f x))
        ≡⟨⟩
      (M ε β ∋ pure (f x)) ∎

    law-interchange : {i : Eff} {α β : Type}
                    → (u : M i (α → β)) (x : α)
                    → (u <*> pure x) ≅ (pure (λ f → f x) <*> u)
    law-interchange {i} {α} {β} u x = begin
      (M (i ∙ ε) β ∋ (u <*> pure x))
        ≡⟨⟩
      (M (i ∙ ε) β ∋ (u >>= (λ f → fmap f (return x))))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) β ∋ u >>= Y) (≡-to-≅ (sym left-id)) (het-fun-ext (≡-to-≅ (fun-ext (λ _ → cong (λ X → M X β) (sym left-id)))) (λ f → hsym (law-monad-fmap f (return x)))) ⟩
      (M (i ∙ (ε ∙ ε)) β ∋ (u >>= (λ f → return x >>= (return ∘ f))))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) β ∋ u >>= Y) (≡-to-≅ left-id) (het-fun-ext (≡-to-≅ (fun-ext (λ _ → cong (λ X → M X β) left-id))) (λ f → law-left-id x (return ∘ f))) ⟩
      (M (i ∙ ε) β ∋ (u >>= (λ f → return (f x))))
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ right-id) (law-monad-fmap (λ f → f x) u) ⟩
      (M i β ∋ fmap (λ f → f x) u)
        ≅⟨ hcong₂ (λ X Y → M X β ∋ Y) (≡-to-≅ (sym left-id)) (hsym (law-left-id (λ f → f x) (λ f → fmap f u))) ⟩
      (M (ε ∙ i) β ∋ (return (λ f → f x) >>= (λ f → fmap f u)))
        ≡⟨⟩
      (M (ε ∙ i) β ∋ (pure (λ f → f x) <*> u)) ∎
