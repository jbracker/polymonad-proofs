 

open import Level

open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )

module Haskell.Parameterized.Indexed.Applicative where

record IxApplicative {ℓ : Level} (Ixs : Set ℓ) (F : Ixs → Ixs → TyCon) : Set (suc zero ⊔ ℓ) where
  constructor indexed-applicative
  infixl 4 _*>_ _<*_ _<*>_ _<$>_
  field
    pure : {α : Type} {i : Ixs} → α → F i i α
    _<*>_ : {α β : Type} {i j k : Ixs} → F i j (α → β) → (F j k α → F i k β)
    
    functor : (i j : Ixs) → Functor (F i j)
  
  field
    law-id : {α : Type} {i j : Ixs}
           → (v : F i j α) 
           → pure (λ x → x) <*> v ≡ v
    
    law-composition : {α β γ : Type} {i j k l : Ixs}
                   → (u : F i j (β → γ)) → (v : F j k (α → β)) → (w : F k l α) 
                   → (pure _∘_) <*> u <*> v <*> w ≡ u <*> (v <*> w)
    
    law-homomorphism : {α β : Type} {i : Ixs}
                     → (x : α) → (f : α → β) 
                     → pure f <*> pure x ≡ pure {i = i} (f x)
    
    law-interchange : {α β : Type} {i j : Ixs}
                    → (u : F i j (α → β)) → (x : α) 
                    → u <*> pure x ≡ pure (λ f → f x) <*> u
    
    law-applicative-fmap : {α β : Type} {i j : Ixs}
                         → (f : α → β) → (x : F i j α) 
                         → (Functor.fmap (functor i j)) f x ≡ pure f <*> x
  
  law-functor-id = λ i j {α} → Functor.law-id (functor i j) {α}
  law-functor-compose = λ i j {α} {β} {γ} → Functor.law-compose (functor i j) {α} {β} {γ}

  fmap : {α β : Type} {i j : Ixs} → (α → β) → F i j α → F i j β
  fmap {i = i} {j} f ma = Functor.fmap (functor i j) f ma
  
  _*>_ : {α β : Type} {i j k : Ixs} → F i j α → F j k β → F i k β
  u *> v = pure (const (id refl)) <*> u <*> v

  _<*_ : {α β : Type} {i j k : Ixs} → F i j α → F j k β → F i k α
  u <* v = pure const <*> u <*> v
  
  _<$>_ = fmap

indexed-applicative-eq 
  : {ℓ : Level} {Ixs : Set ℓ} {F : Ixs → Ixs → TyCon}
  → {pure₀ : {α : Type} {i : Ixs} → α → F i i α}
  → {pure₁ : {α : Type} {i : Ixs} → α → F i i α}
  → {_<*>₀_ : {α β : Type} {i j k : Ixs} → F i j (α → β) → (F j k α → F i k β)}
  → {_<*>₁_ : {α β : Type} {i j k : Ixs} → F i j (α → β) → (F j k α → F i k β)}
  → {functor₀ : (i j : Ixs) → Functor (F i j)}
  → {functor₁ : (i j : Ixs) → Functor (F i j)}
  → {law-id₀ : {α : Type} {i j : Ixs} → (v : F i j α) → pure₀ (λ x → x) <*>₀ v ≡ v}
  → {law-id₁ : {α : Type} {i j : Ixs} → (v : F i j α) → pure₁ (λ x → x) <*>₁ v ≡ v}
  → {law-composition₀ : {α β γ : Type} {i j k l : Ixs} → (u : F i j (β → γ)) → (v : F j k (α → β)) → (w : F k l α) → (((pure₀ _∘_) <*>₀ u) <*>₀ v) <*>₀ w ≡ u <*>₀ (v <*>₀ w)}
  → {law-composition₁ : {α β γ : Type} {i j k l : Ixs} → (u : F i j (β → γ)) → (v : F j k (α → β)) → (w : F k l α) → (((pure₁ _∘_) <*>₁ u) <*>₁ v) <*>₁ w ≡ u <*>₁ (v <*>₁ w)}
  → {law-homomorphism₀ : {α β : Type} {i : Ixs} → (x : α) → (f : α → β) → pure₀ f <*>₀ pure₀ x ≡ pure₀ {i = i} (f x)}
  → {law-homomorphism₁ : {α β : Type} {i : Ixs} → (x : α) → (f : α → β) → pure₁ f <*>₁ pure₁ x ≡ pure₁ {i = i}(f x)}
  → {law-interchange₀ : {α β : Type} {i j : Ixs} → (u : F i j (α → β)) → (x : α) → u <*>₀ pure₀ x ≡ pure₀ (λ f → f x) <*>₀ u}
  → {law-interchange₁ : {α β : Type} {i j : Ixs} → (u : F i j (α → β)) → (x : α) → u <*>₁ pure₁ x ≡ pure₁ (λ f → f x) <*>₁ u}
  → {law-applicative-fmap₀ : {α β : Type} {i j : Ixs} → (f : α → β) → (x : F i j α) → (Functor.fmap (functor₀ i j)) f x ≡ pure₀ f <*>₀ x}
  → {law-applicative-fmap₁ : {α β : Type} {i j : Ixs} → (f : α → β) → (x : F i j α) → (Functor.fmap (functor₁ i j)) f x ≡ pure₁ f <*>₁ x}
  → (λ {α} {i} → pure₀ {α} {i}) ≡ pure₁
  → (λ {α β} {i j k} → _<*>₀_ {α} {β} {i} {j} {k}) ≡ _<*>₁_
  → (λ i j → functor₀ i j) ≡ (λ i j → functor₁ i j)
  → indexed-applicative {F = F} pure₀ _<*>₀_ functor₀ law-id₀ law-composition₀ law-homomorphism₀ law-interchange₀ law-applicative-fmap₀
  ≡ indexed-applicative {F = F} pure₁ _<*>₁_ functor₁ law-id₁ law-composition₁ law-homomorphism₁ law-interchange₁ law-applicative-fmap₁
indexed-applicative-eq {ℓ} {Ixs} {F} {p} {.p} {ap} {.ap} {f} {.f} {li₀} {li₁} {co₀} {co₁} {hom₀} {hom₁} {in₀} {in₁} {af₀} {af₁} refl refl refl
  = cong₅ (indexed-applicative p ap f) p1 p2 p3 p4 p5
  where
    p1 : (λ {α} {i j} → li₀ {α} {i} {j}) ≡ li₁
    p1 = implicit-fun-ext $ λ α → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → fun-ext $ λ fa → proof-irrelevance (li₀ {α} {i} {j} fa) (li₁ {α} {i} {j} fa)

    p2 : (λ {α β γ} {i j k l} → co₀ {α} {β} {γ} {i} {j} {k} {l}) ≡ co₁
    p2 = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ γ → implicit-fun-ext 
       $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → implicit-fun-ext $ λ l → fun-ext
       $ λ f → fun-ext $ λ g → fun-ext $ λ a → proof-irrelevance (co₀ {α} {β} {γ} {i} {j} {k} {l} f g a) (co₁ f g a)
   
    p3 : (λ {α β} {i} → hom₀ {α} {β} {i}) ≡ hom₁
    p3 = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext 
       $ λ i → fun-ext
       $ λ a → fun-ext $ λ f → proof-irrelevance (hom₀ {α} {β} {i} a f) (hom₁ a f)
    
    p4 : (λ {α β} {i j} → in₀ {α} {β} {i} {j}) ≡ in₁
    p4 = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext 
       $ λ i → implicit-fun-ext $ λ j → fun-ext
       $ λ f → fun-ext $ λ a → proof-irrelevance (in₀ {α} {β} {i} {j} f a) (in₁ f a)

    p5 : (λ {α β} {i j} → af₀ {α} {β} {i} {j}) ≡ af₁
    p5 = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext 
       $ λ i → implicit-fun-ext $ λ j → fun-ext
       $ λ f → fun-ext $ λ a → proof-irrelevance (af₀ {α} {β} {i} {j} f a) (af₁ f a)

