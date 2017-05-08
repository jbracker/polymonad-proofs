 
module Haskell.Applicative where

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )

record Applicative (F : TyCon) : Set₁ where
  constructor applicative
  infixl 4 _*>_ _<*_ _<*>_ _<$>_
  field
    pure : ∀ {α : Type} → α → F α
    _<*>_ : ∀ {α β : Type} → F (α → β) → F α → F β
    
    functor : Functor F

  open Functor functor renaming ( law-id to law-functor-id ) public
  
  field
    law-id  : ∀ {α : Type} 
           → (v : F α) 
           → pure (λ x → x) <*> v ≡ v
    law-composition : ∀ {α β γ : Type} 
                   → (u : F (β → γ)) → (v : F (α → β)) → (w : F α) 
                   → (pure _∘_) <*> u <*> v <*> w ≡ u <*> (v <*> w)
    law-homomorphism : ∀ {α β : Type} 
                    → (x : α) → (f : α → β) 
                    → pure f <*> pure x ≡ pure (f x)
    law-interchange : ∀ {α β : Type} 
                   → (u : F (α → β)) → (x : α) 
                   → u <*> pure x ≡ pure (λ f → f x) <*> u
    
    law-applicative-fmap : ∀ {α β : Type} 
                       → (f : α → β) → (x : F α) 
                       → (Functor.fmap functor) f x ≡ pure f <*> x
  
  _*>_ : ∀ {α β : Type} → F α → F β → F β
  u *> v = pure (const (id refl)) <*> u <*> v

  _<*_ : ∀ {α β : Type} → F α → F β → F α
  u <* v = pure const <*> u <*> v
  
  _<$>_ = fmap


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
    p1 : (λ {α} → li₀ {α}) ≡ li₁
    p1 = implicit-fun-ext (λ α → fun-ext (λ fa → proof-irrelevance (li₀ fa) (li₁ fa)))

    p2 : (λ {α β γ} → co₀ {α} {β} {γ}) ≡ co₁
    p2 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → implicit-fun-ext (λ γ → fun-ext
       $ λ f → fun-ext (λ g → fun-ext (λ a → proof-irrelevance (co₀ f g a) (co₁ f g a))))))
   
    p3 : (λ {α β} → hom₀ {α} {β}) ≡ hom₁
    p3 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
       $ λ a → fun-ext (λ f → proof-irrelevance (hom₀ a f) (hom₁ a f))))
    
    p4 : (λ {α β} → in₀ {α} {β}) ≡ in₁
    p4 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
       $ λ f → fun-ext (λ a → proof-irrelevance (in₀ f a) (in₁ f a))))

    p5 : (λ {α β} → af₀ {α} {β}) ≡ af₁
    p5 = implicit-fun-ext (λ α → implicit-fun-ext (λ β → fun-ext
       $ λ f → fun-ext (λ a → proof-irrelevance (af₀ f a) (af₁ f a))))

applicativeFromMonad : ∀ {M : TyCon}
                     → (_>>=_ : [ M , M ]▷ M)
                     → (return : ∀ {α : Type} → α → M α)
                     → (law-left-id : ∀ {α : Type} 
                               → (m : M α)
                               → m >>= return ≡ m)
                     → (law-right-id : ∀ {α β : Type} 
                               → (a : α) → (k : α → M β) 
                               → return a >>= k ≡ k a)
                     → (law-assoc : ∀ {α β γ : Type} 
                                 → (m : M α) → (k : α → M β) → (h : β → M γ)
                                 → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h)
                     → Applicative M
applicativeFromMonad {M = M} _>>=_ return law-left-id law-right-id law-assoc = record
  { pure = return
  ; _<*>_ = apM
  ; functor = functor
  ; law-id = law-id
  ; law-composition = law-composition
  ; law-homomorphism = law-homomorphism
  ; law-interchange = law-interchange
  ; law-applicative-fmap = law-applicative-fmap
  } where
    apM : ∀ {α β : Type} → M (α → β) → M α → M β
    apM f x = f >>= (λ f → x >>= (return ∘ f))

    functor : Functor M
    functor = functorFromMonad _>>=_ return law-left-id law-right-id law-assoc

    law-id : ∀ {α : Type} 
          → (v : M α) 
          → apM (return (id refl)) v ≡ v
    law-id v = begin 
      apM (return (id refl)) v 
        ≡⟨ refl ⟩ 
      (return (id refl)) >>= (λ f → v >>= (λ a → return (f a)))
        ≡⟨ law-right-id (id refl) ((λ f → v >>= (λ a → return (f a)))) ⟩ 
      v >>= return
        ≡⟨ law-left-id v ⟩ 
      v ∎

    law-composition : ∀ {α β γ : Type} 
                   → (u : M (β → γ)) → (v : M (α → β)) → (w : M α) 
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

    law-homomorphism : ∀ {α β : Type} 
                    → (x : α) → (f : α → β) 
                    → apM (return f) (return x) ≡ return (f x)
    law-homomorphism x f = begin 
      apM (return f) (return x) 
        ≡⟨ refl ⟩ 
      (return f) >>= (λ f → (return x) >>= (λ a → return (f a) ) )
        ≡⟨ law-right-id f ((λ f → (return x) >>= (λ a → return (f a) ) )) ⟩ 
      (return x) >>= (λ a → return (f a) )
        ≡⟨ law-right-id x ((λ a → return (f a) )) ⟩ 
      return (f x) ∎

    law-interchange : ∀ {α β : Type} 
                   → (u : M (α → β)) → (x : α) 
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

    law-applicative-fmap : ∀ {α β : Type} 
                       → (f : α → β) → (x : M α) 
                       → Functor.fmap functor f x ≡ apM (return f) x
    law-applicative-fmap f x = begin
      Functor.fmap functor f x 
        ≡⟨ refl ⟩ 
      x >>= (return ∘ f)
        ≡⟨ sym (law-right-id f (λ g → x >>= (return ∘ g))) ⟩ 
      (return f) >>= (λ g → x >>= (return ∘ g) )
        ≡⟨ refl ⟩ 
      apM (return f) x ∎
