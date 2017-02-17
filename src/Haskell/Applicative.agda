 
module Haskell.Applicative where

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Identity
open import Haskell 
open import Haskell.Functor

record Applicative (F : TyCon) : Set₁ where
  infixl 4 _*>_ _<*_ _<*>_
  field
    pure : ∀ {α : Type} → α → F α
    _<*>_ : ∀ {α β : Type} → F (α → β) → F α → F β
    
    functor : Functor F
    
    lawId  : ∀ {α : Type} 
           → (v : F α) 
           → pure (id refl) <*> v ≡ v
    lawComposition : ∀ {α β γ : Type} 
                   → (u : F (β → γ)) → (v : F (α → β)) → (w : F α) 
                   → (pure _∘_) <*> u <*> v <*> w ≡ u <*> (v <*> w)
    lawHomomorphism : ∀ {α β : Type} 
                    → (x : α) → (f : α → β) 
                    → pure f <*> pure x ≡ pure (f x)
    lawInterchange : ∀ {α β : Type} 
                   → (u : F (α → β)) → (x : α) 
                   → u <*> pure x ≡ pure (λ f → f x) <*> u
    
    lawApplicativeFmap : ∀ {α β : Type} 
                       → (f : α → β) → (x : F α) 
                       → (Functor.fmap functor) f x ≡ pure f <*> x
  
  _*>_ : ∀ {α β : Type} → F α → F β → F β
  u *> v = pure (const (id refl)) <*> u <*> v

  _<*_ : ∀ {α β : Type} → F α → F β → F α
  u <* v = pure const <*> u <*> v

applicativeFromMonad : ∀ {M : TyCon}
                     → (_>>=_ : [ M , M ]▷ M)
                     → (return : ∀ {α : Type} → α → M α)
                     → (lawIdL : ∀ {α : Type} 
                               → (m : M α)
                               → m >>= return ≡ m)
                     → (lawIdR : ∀ {α β : Type} 
                               → (a : α) → (k : α → M β) 
                               → return a >>= k ≡ k a)
                     → (lawAssoc : ∀ {α β γ : Type} 
                                 → (m : M α) → (k : α → M β) → (h : β → M γ)
                                 → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h)
                     → Applicative M
applicativeFromMonad {M = M} _>>=_ return lawIdL lawIdR lawAssoc = record
  { pure = return
  ; _<*>_ = apM
  ; functor = functor
  ; lawId = lawId
  ; lawComposition = lawComposition
  ; lawHomomorphism = lawHomomorphism
  ; lawInterchange = lawInterchange
  ; lawApplicativeFmap = lawApplicativeFmap
  } where
    apM : ∀ {α β : Type} → M (α → β) → M α → M β
    apM f x = f >>= (λ f → x >>= (return ∘ f))

    functor : Functor M
    functor = functorFromMonad _>>=_ return lawIdL lawIdR lawAssoc

    lawId : ∀ {α : Type} 
          → (v : M α) 
          → apM (return (id refl)) v ≡ v
    lawId v = begin 
      apM (return (id refl)) v 
        ≡⟨ refl ⟩ 
      (return (id refl)) >>= (λ f → v >>= (λ a → return (f a)))
        ≡⟨ lawIdR (id refl) ((λ f → v >>= (λ a → return (f a)))) ⟩ 
      v >>= return
        ≡⟨ lawIdL v ⟩ 
      v ∎

    lawComposition : ∀ {α β γ : Type} 
                   → (u : M (β → γ)) → (v : M (α → β)) → (w : M α) 
                   → apM (apM (apM (return _∘_) u) v) w ≡ apM u (apM v w)
    lawComposition u v w = begin
      apM (apM (apM (return _∘_) u) v) w 
        ≡⟨ refl ⟩
      (((return _∘_) >>= (λ h → u >>= (return ∘ h))) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ cong (λ X → (X >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))) (lawIdR _∘_ ((λ h → u >>= (return ∘ h)))) ⟩
      ((u >>= (λ a → return (_∘_ a))) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ cong (λ X → X >>= (λ f → w >>= (return ∘ f))) (sym (lawAssoc u (return ∘ _∘_) ((λ g → v >>= (return ∘ g))))) ⟩
      ( u >>= (λ x → return (_∘_ x) >>= (λ g → v >>= (return ∘ g)) ) ) >>= (λ f → w >>= (return ∘ f))
        ≡⟨ sym (lawAssoc u ((λ x → return (_∘_ x) >>= (λ g → v >>= (return ∘ g)) )) ((λ f → w >>= (return ∘ f)))) ⟩
      u >>= (λ f → (return (_∘_ f) >>= (λ g → v >>= (return ∘ g))) >>= (λ f → w >>= (return ∘ f)) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → X >>= (λ f → w >>= (return ∘ f))) (lawIdR ((_∘_ f)) ((λ g → v >>= (return ∘ g)))))) ⟩
      u >>= (λ f → (v >>= (λ g → return (f ∘ g))) >>= (λ h → w >>= (return ∘ h)) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → sym (lawAssoc v (λ g → return (f ∘ g)) ((λ h → w >>= (return ∘ h)))))) ⟩
      u >>= (λ f → v >>= (λ g → return (f ∘ g) >>= (λ h → w >>= (return ∘ h)) ) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → lawIdR (f ∘ g) ((λ h → w >>= (return ∘ h))))))) ⟩
      u >>= (λ f → v >>= (λ g → w >>= (return ∘ (f ∘ g)) ) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → cong (λ X → w >>= X) (funExt (λ x → sym (lawIdR (g x) (return ∘ f)))))))) ⟩
      u >>= (λ f → v >>= (λ g → w >>= (λ x → return (g x) >>= (return ∘ f)) ) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → lawAssoc w (return ∘ g) (return ∘ f))))) ⟩
      u >>= (λ f → v >>= (λ g → (w >>= (return ∘ g)) >>= (return ∘ f) ) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → lawAssoc v ((λ g → w >>= (return ∘ g))) (return ∘ f))) ⟩
      apM u (apM v w) ∎

    lawHomomorphism : ∀ {α β : Type} 
                    → (x : α) → (f : α → β) 
                    → apM (return f) (return x) ≡ return (f x)
    lawHomomorphism x f = begin 
      apM (return f) (return x) 
        ≡⟨ refl ⟩ 
      (return f) >>= (λ f → (return x) >>= (λ a → return (f a) ) )
        ≡⟨ lawIdR f ((λ f → (return x) >>= (λ a → return (f a) ) )) ⟩ 
      (return x) >>= (λ a → return (f a) )
        ≡⟨ lawIdR x ((λ a → return (f a) )) ⟩ 
      return (f x) ∎

    lawInterchange : ∀ {α β : Type} 
                   → (u : M (α → β)) → (x : α) 
                   → apM u (return x) ≡ apM (return (λ f → f x)) u
    lawInterchange u x = begin
      apM u (return x) 
        ≡⟨ refl ⟩
      u >>= (λ f → (return x) >>= (return ∘ f) )
        ≡⟨ cong (λ X → u >>= X) (funExt (λ f → lawIdR x (return ∘ f))) ⟩
      u >>= (λ f → (return ∘ f) x )
        ≡⟨ refl ⟩
      u >>= (return ∘ (λ f → f x))
        ≡⟨ sym (lawIdR (λ f → f x) ((λ g → u >>= (return ∘ g) ))) ⟩
      (return (λ f → f x)) >>= (λ g → u >>= (return ∘ g) )
        ≡⟨ refl ⟩
      apM (return (λ f → f x)) u ∎

    lawApplicativeFmap : ∀ {α β : Type} 
                       → (f : α → β) → (x : M α) 
                       → Functor.fmap functor f x ≡ apM (return f) x
    lawApplicativeFmap f x = begin
      Functor.fmap functor f x 
        ≡⟨ refl ⟩ 
      x >>= (return ∘ f)
        ≡⟨ sym (lawIdR f (λ g → x >>= (return ∘ g))) ⟩ 
      (return f) >>= (λ g → x >>= (return ∘ g) )
        ≡⟨ refl ⟩ 
      apM (return f) x ∎
