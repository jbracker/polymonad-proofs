
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
    law-composition {i} {j} {k} {α} {β} {γ} u v w = begin
      (M (((ε ∙ i) ∙ j) ∙ k) γ ∋ (((pure _∘_ <*> u) <*> v) <*> w))
        ≡⟨⟩
      (M (((ε ∙ i) ∙ j) ∙ k) γ ∋ (((return _∘_ >>= (λ h → fmap h u)) >>= (λ f → fmap f v)) >>= (λ g → fmap g w)))
        ≅⟨ hcong₂ (λ X Y → M ((X ∙ j) ∙ k) γ ∋ ((Y >>= (λ f → fmap f v)) >>= (λ g → fmap g w))) (≡-to-≅ left-id) (law-left-id _∘_ (λ h → fmap h u)) ⟩
      (M ((i ∙ j) ∙ k) γ ∋ (((fmap _∘_ u) >>= (λ f → fmap f v)) >>= (λ g → fmap g w)))
        ≅⟨ hcong₂ (λ X Y → M ((X ∙ j) ∙ k) γ ∋ (Y >>= (λ f → fmap f v)) >>= (λ g → fmap g w)) (≡-to-≅ (sym right-id)) (hsym (law-monad-fmap _∘_ u)) ⟩
      (M (((i ∙ ε) ∙ j) ∙ k) γ ∋ (((u >>= (return ∘ _∘_)) >>= (λ f → fmap f v)) >>= (λ g → fmap g w)))
        ≅⟨ hcong₂ (λ X Y → M (X ∙ k) γ ∋ Y >>= (λ g → fmap g w)) (≡-to-≅ (sym assoc)) (hsym (law-assoc u (return ∘ _∘_) (λ f → fmap f v))) ⟩
      (M ((i ∙ (ε ∙ j)) ∙ k) γ ∋ ((u >>= (λ x → return (_∘_ x) >>= (λ f → fmap f v) )) >>= (λ g → fmap g w)))
        ≅⟨ hcong₂ (λ X Y → M X γ ∋ Y) (≡-to-≅ (sym assoc)) (hsym (law-assoc u (λ x → return (_∘_ x) >>= (λ f → fmap f v)) (λ g → fmap g w))) ⟩
      (M (i ∙ ((ε ∙ j) ∙ k)) γ ∋ (u >>= (λ f → (return (_∘_ f) >>= (λ f → fmap f v)) >>= (λ g → fmap g w) ) ))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ (u >>= Y))
                  (≡-to-≅ $ cong (λ X → X ∙ k) left-id)
                  (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M (X ∙ k) γ)) left-id))
                               (λ f → hcong₂ (λ X Y → M (X ∙ k) γ ∋ Y >>= (λ g → fmap g w))
                                             (≡-to-≅ left-id)
                                             (law-left-id (_∘_ f) (λ f → fmap f v)))) ⟩
      (M (i ∙ (j ∙ k)) γ ∋ (u >>= (λ f → (fmap (_∘_ f) v) >>= (λ g → fmap g w) ) ))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ (u >>= Y))
                  (≡-to-≅ $ cong (λ X → X ∙ k) (sym right-id))
                  (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M (X ∙ k) γ)) (sym right-id)))
                               (λ f → hcong₂ (λ X Y → M (X ∙ k) γ ∋ Y >>= (λ g → fmap g w))
                                             (≡-to-≅ (sym right-id))
                                             (hsym (law-monad-fmap (_∘_ f) v)))) ⟩
      (M (i ∙ ((j ∙ ε) ∙ k)) γ ∋ (u >>= (λ f → (v >>= (return ∘ (_∘_ f))) >>= (λ g → fmap g w) ) ))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ (u >>= Y))
                  (≡-to-≅ (sym assoc))
                  (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M X γ)) (sym assoc)))
                               (λ f → hsym (law-assoc v (return ∘ (_∘_ f)) (λ g → fmap g w)) )) ⟩
      (M (i ∙ (j ∙ (ε ∙ k))) γ ∋ (u >>= (λ f → v >>= (λ x → return (f ∘ x) >>= (λ g → fmap g w)) ) ))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ (u >>= Y))
                  (≡-to-≅ (cong (_∙_ j) left-id))
                  (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M X γ)) (cong (_∙_ j) left-id)))
                               (λ f → hcong₂ (λ X Y → M (j ∙ X) γ ∋ (v >>= Y))
                                             (≡-to-≅ left-id)
                                             (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M X γ)) left-id))
                                                          (λ x → law-left-id (f ∘ x) (λ g → fmap g w))))) ⟩
      (M (i ∙ (j ∙ k)) γ ∋ (u >>= (λ f → v >>= (λ x → fmap (f ∘ x) w) ) ))
        ≅⟨ ≡-to-≅ (cong (λ X → _>>=_ u X) (fun-ext (λ f → cong (λ X → _>>=_ v X) (fun-ext (λ x → cong (λ X → X w) (Functor.law-compose (functor k) f x)))))) ⟩
      (M (i ∙ (j ∙ k)) γ ∋ (u >>= (λ f → v >>= (λ x → fmap f (fmap x w) ) )))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ u >>= Y)
                  (≡-to-≅ $ cong (_∙_ j) (sym right-id))
                  (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M (j ∙ X) γ)) (sym right-id)))
                               (λ f → hcong₂ (λ X Y → M (j ∙ X) γ ∋ v >>= Y)
                                             (≡-to-≅ (sym right-id))
                                             (het-fun-ext (≡-to-≅ (cong (λ X → (λ _ → M X γ)) (sym right-id)))
                                                          (λ x → hsym (law-monad-fmap f (fmap x w)))))) ⟩
      (M (i ∙ (j ∙ (k ∙ ε))) γ ∋ (u >>= (λ f → v >>= (λ x → fmap x w >>= (return ∘ f) ) )))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ u >>= Y) (≡-to-≅ assoc) (het-fun-ext (≡-to-≅ (fun-ext (λ _ → cong (λ X → M X γ) assoc))) (λ f → law-assoc v (λ g → fmap g w) (return ∘ f))) ⟩
      (M (i ∙ ((j ∙ k) ∙ ε)) γ ∋ (u >>= (λ f → (v >>= (λ g → fmap g w)) >>= (return ∘ f) )))
        ≅⟨ hcong₂ (λ X Y → M (i ∙ X) γ ∋ u >>= Y) (≡-to-≅ right-id) (het-fun-ext (≡-to-≅ (fun-ext (λ _ → cong (λ X → M X γ) right-id))) (λ f → law-monad-fmap f (v >>= (λ g → fmap g w)))) ⟩
      (M (i ∙ (j ∙ k)) γ ∋ (u >>= (λ f → fmap f (v >>= (λ g → fmap g w)))))
        ≡⟨⟩
      (M (i ∙ (j ∙ k)) γ ∋ (u <*> (v <*> w))) ∎
    
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
