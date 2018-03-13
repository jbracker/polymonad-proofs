
open import Level

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )
open import Haskell.Parameterized.Indexed.Applicative
open import Haskell.Parameterized.Indexed.Monad

module Haskell.Parameterized.Indexed.Applicative.FromIndexedMonad where

IxMonad→IxApplicative
  : {ℓ : Level} {Ixs : Set ℓ} {M : Ixs → Ixs → TyCon}
  → IxMonad Ixs M → IxApplicative Ixs M
IxMonad→IxApplicative {ℓ} {Ixs} {M} monad = record
  { pure = return
  ; _<*>_ = apM
  ; functor = functor
  ; law-id = law-id
  ; law-composition = law-composition
  ; law-homomorphism = law-homomorphism
  ; law-interchange = law-interchange
  ; law-applicative-fmap = law-applicative-fmap
  } where
    open IxMonad monad renaming ( functor to monad-functor )
    
    apM : {α β : Type} {i j k : Ixs} → M i j (α → β) → M j k α → M i k β
    apM f x = f >>= (λ f → x >>= (return ∘ f))

    functor : (i j : Ixs) → Functor (M i j)
    functor i j = monad-functor i j

    law-id : {α : Type} {i j : Ixs}
           → (v : M i j α) 
           → apM (return (id refl)) v ≡ v
    law-id v = begin 
      apM (return (id refl)) v 
        ≡⟨ refl ⟩ 
      (return (id refl)) >>= (λ f → v >>= (λ a → return (f a)))
        ≡⟨ law-right-id (id refl) ((λ f → v >>= (λ a → return (f a)))) ⟩ 
      v >>= return
        ≡⟨ law-left-id v ⟩ 
      v ∎

    law-composition : {α β γ : Type} {i j k l : Ixs}
                    → (u : M i j (β → γ)) → (v : M j k (α → β)) → (w : M k l α) 
                    → apM (apM (apM (return _∘_) u) v) w ≡ apM u (apM v w)
    law-composition u v w = begin
      apM (apM (apM (return _∘_) u) v) w 
        ≡⟨ refl ⟩
      (((return _∘_) >>= (λ h → u >>= (return ∘ h))) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ cong (λ X → (X >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))) (law-right-id _∘_ ((λ h → u >>= (return ∘ h)))) ⟩
      ((u >>= (λ a → return (_∘_ a))) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ cong (λ X → X >>= (λ f → w >>= (return ∘ f))) (sym (law-assoc u (return ∘ _∘_) ((λ g → v >>= (return ∘ g))))) ⟩
      ( u >>= (λ x → return (_∘_ x) >>= (λ g → v >>= (return ∘ g)) ) ) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ sym (law-assoc u ((λ x → return (_∘_ x) >>= (λ g → v >>= (return ∘ g)) )) ((λ f → w >>= (return ∘ f)))) ⟩
      u >>= (λ f → (return (_∘_ f) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f)) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → X >>= (λ f → w >>= (return ∘ f))) (law-right-id ((_∘_ f)) ((λ g → v >>= (return ∘ g)))))) ⟩
      u >>= (λ f → (v >>= (λ g → return (f ∘ g))) >>= (λ h → w >>= (return ∘ h)) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → sym (law-assoc v (λ g → return (f ∘ g)) ((λ h → w >>= (return ∘ h)))))) ⟩
      u >>= (λ f → v >>= (λ g → return (f ∘ g) >>= (λ h → w >>= (return ∘ h)) ) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → law-right-id (f ∘ g) ((λ h → w >>= (return ∘ h))))))) ⟩
      u >>= (λ f → v >>= (λ g → w >>= (return ∘ (f ∘ g)) ) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → cong (λ X → w >>= X) (fun-ext (λ x → sym (law-right-id (g x) (return ∘ f)))))))) ⟩
      u >>= (λ f → v >>= (λ g → w >>= (λ x → return (g x) >>= (return ∘ f)) ) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → law-assoc w (return ∘ g) (return ∘ f))))) ⟩
      u >>= (λ f → v >>= (λ g → (w >>= (return ∘ g)) >>= (return ∘ f) ) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → law-assoc v ((λ g → w >>= (return ∘ g))) (return ∘ f))) ⟩
      apM u (apM v w) ∎

    law-homomorphism : {α β : Type} {i : Ixs}
                    → (x : α) → (f : α → β) 
                    → apM (return f) (return x) ≡ return {i = i} (f x)
    law-homomorphism x f = begin 
      apM (return f) (return x) 
        ≡⟨ refl ⟩ 
      (return f) >>= (λ f → (return x) >>= (λ a → return (f a) ) )
        ≡⟨ law-right-id f ((λ f → (return x) >>= (λ a → return (f a) ) )) ⟩ 
      (return x) >>= (λ a → return (f a) )
        ≡⟨ law-right-id x ((λ a → return (f a) )) ⟩ 
      return (f x) ∎

    law-interchange : {α β : Type} {i j : Ixs}
                   → (u : M i j (α → β)) → (x : α) 
                   → apM u (return x) ≡ apM (return (λ f → f x)) u
    law-interchange u x = begin
      apM u (return x) 
        ≡⟨ refl ⟩
      u >>= (λ f → (return x) >>= (return ∘ f) )
        ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → law-right-id x (return ∘ f))) ⟩
      u >>= (λ f → (return ∘ f) x )
        ≡⟨ refl ⟩
      u >>= (return ∘ (λ f → f x))
        ≡⟨ sym (law-right-id (λ f → f x) ((λ g → u >>= (return ∘ g) ))) ⟩
      (return (λ f → f x)) >>= (λ g → u >>= (return ∘ g) )
        ≡⟨ refl ⟩
      apM (return (λ f → f x)) u ∎

    law-applicative-fmap : {α β : Type} {i j : Ixs}
                         → (f : α → β) → (x : M i j α) 
                         → Functor.fmap (functor i j) f x ≡ apM (return f) x
    law-applicative-fmap {i = i} {j} f x = begin
      Functor.fmap (functor i j) f x 
        ≡⟨ sym (law-monad-fmap f x) ⟩ 
      x >>= (return ∘ f)
        ≡⟨ sym (law-right-id f (λ g → x >>= (return ∘ g))) ⟩ 
      (return f) >>= (λ g → x >>= (return ∘ g) )
        ≡⟨ refl ⟩ 
      apM (return f) x ∎

