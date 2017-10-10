 

open import Level
open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )

open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality
open import Congruence
open import Identity
open import Haskell 
open import Haskell.Functor hiding ( functor )
open import Haskell.Applicative using ( _***_ )

module Haskell.Parameterized.Indexed.Applicative where

record IxApplicative {ℓ : Level} (Ixs : Set ℓ) (F : Ixs → Ixs → TyCon) : Set (suc zero ⊔ ℓ) where
  constructor indexed-applicative
  infixl 5 _*>_ _<*_ _<*>_ _<$>_
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

  _**_ : {α β : Type} {i j k : Ixs} → F i j α → F j k β → F i k (α × β)
  fa ** fb = fmap (λ a b → a , b) fa <*> fb
  
  unit : {i : Ixs} → F i i ⊤
  unit = pure tt 
  
  abstract
    law-naturality : {i j k : Ixs} {α β γ δ : Type} 
                   → (f : α → β) (g : γ → δ) (u : F i j α) (v : F j k γ) 
                   → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
    law-naturality f g u v = begin
      fmap (f *** g) (u ** v) 
        ≡⟨ law-applicative-fmap (f *** g) (u ** v) ⟩
      pure (f *** g) <*> (fmap (_,_) u <*> v) 
        ≡⟨ cong (λ X → pure (f *** g) <*> (X <*> v) ) (law-applicative-fmap _,_ u) ⟩
      pure (f *** g) <*> (pure (_,_) <*> u <*> v) 
        ≡⟨ sym (law-composition (pure (f *** g)) (pure (_,_) <*> u) v) ⟩
      pure (_∘_) <*> pure (f *** g) <*> (pure (_,_) <*> u) <*> v 
        ≡⟨ cong (λ X → X <*> (pure (_,_) <*> u) <*> v) (law-homomorphism (f *** g) _∘_) ⟩
      pure (_∘_ (f *** g)) <*> (pure (_,_) <*> u) <*> v 
        ≡⟨ cong (λ X → X <*> v) (sym (law-composition (pure (_∘_ (f *** g))) (pure (_,_)) u)) ⟩
      pure (_∘_) <*> pure (_∘_ (f *** g)) <*> pure (_,_) <*> u <*> v 
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> u <*> v) (law-homomorphism (_∘_ (f *** g)) _∘_) ⟩
      pure (_∘_ (_∘_ (f *** g))) <*> pure (_,_) <*> u <*> v 
        ≡⟨ cong (λ X → X <*> u <*> v) (law-homomorphism _,_ (_∘_ (_∘_ (f *** g)))) ⟩
      pure ((_∘_ (f *** g)) ∘ (_,_)) <*> u <*> v 
        ≡⟨ refl ⟩ -- Of course, how obvious...
      pure (_∘_ (λ h → h g) ((_∘_) ∘ ((_,_) ∘ f))) <*> u <*> v
        ≡⟨ cong (λ X → X <*> u <*> v)  (sym (law-homomorphism ((_∘_) ∘ ((_,_) ∘ f)) (_∘_ (λ h → h g)))) ⟩
      pure (_∘_ (λ h → h g)) <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v
        ≡⟨ cong (λ X → X <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v) (sym (law-homomorphism (λ h → h g) _∘_)) ⟩
      pure (_∘_) <*> pure (λ h → h g) <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v
        ≡⟨ cong (λ X → X <*> v) (law-composition (pure (λ h → h g)) (pure ((_∘_) ∘ ((_,_) ∘ f))) u) ⟩
      pure (λ h → h g) <*> (pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u) <*> v
        ≡⟨ cong (λ X → X <*> v) (sym (law-interchange (pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u) g)) ⟩
      pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> pure g <*> v
        ≡⟨ cong (λ X → X <*> u <*> pure g <*> v) (sym (law-homomorphism ((_,_) ∘ f) (_∘_ (_∘_)))) ⟩
      pure (_∘_ (_∘_)) <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v
        ≡⟨ cong (λ X → X <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v) (sym (law-homomorphism _∘_ _∘_)) ⟩
      pure (_∘_) <*> pure (_∘_) <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v
        ≡⟨ cong (λ X → X <*> pure g <*> v) (law-composition (pure (_∘_)) (pure ((_,_) ∘ f)) u) ⟩
      pure (_∘_) <*> (pure ((_,_) ∘ f) <*> u) <*> pure g <*> v
        ≡⟨ law-composition (pure ((_,_) ∘ f) <*> u) (pure g) v ⟩
      pure ((_,_) ∘ f) <*> u <*> (pure g <*> v)
        ≡⟨ cong (λ X → X <*> u <*> (pure g <*> v)) (sym (law-homomorphism f (_∘_ (_,_)))) ⟩
      pure (_∘_ (_,_)) <*> pure f <*> u <*> (pure g <*> v)
        ≡⟨ cong (λ X → X <*> pure f <*> u <*> (pure g <*> v)) (sym (law-homomorphism _,_ _∘_)) ⟩
      pure (_∘_) <*> pure (_,_) <*> pure f <*> u <*> (pure g <*> v)
        ≡⟨ cong (λ X → X <*> (pure g <*> v)) (law-composition (pure (_,_)) (pure f) u) ⟩
      pure (_,_) <*> (pure f <*> u) <*> (pure g <*> v)
        ≡⟨ cong (λ X → X <*> (pure g <*> v)) (sym (law-applicative-fmap _,_ (pure f <*> u))) ⟩
      fmap (_,_) (pure f <*> u) <*> (pure g <*> v)
        ≡⟨ cong₂ (λ X Y → X ** Y) (sym (law-applicative-fmap f u)) (sym (law-applicative-fmap g v)) ⟩
      fmap f u ** fmap g v ∎

  abstract
    law-left-identity : {i j : Ixs} {α : Type} → (v : F i j α) 
                      → unit ** v ≡ fmap (λ a → (tt , a)) v
    law-left-identity v = begin
      unit ** v 
        ≡⟨⟩
      fmap (_,_) (pure (tt)) <*> v 
        ≡⟨ cong (λ X → X <*> v) (law-applicative-fmap _,_ (pure (tt))) ⟩
      pure (_,_) <*> pure (tt) <*> v 
        ≡⟨ cong (λ X → X <*> v) (law-homomorphism (tt) _,_) ⟩
      pure (λ a → (tt , a)) <*> v
        ≡⟨ sym (law-applicative-fmap (λ a → (tt , a)) v) ⟩
      fmap (λ a → (tt , a)) v ∎
    
  abstract
    law-left-identity' : {i j : Ixs} {α : Type} → (v : F i j α) 
                       → fmap proj₂ (unit ** v) ≡ v
    law-left-identity' {i} {j} {α} v 
      = trans (cong (λ X → fmap proj₂ X) (law-left-identity v)) 
              (trans (cong (λ X → X v) (sym $ law-functor-compose i j proj₂ (λ a → tt , a))) 
                     (cong (λ X → X v) (law-functor-id i j))) 
  
  abstract
    law-right-identity : {i j : Ixs} {α : Type} → (v : F i j α) 
                       → v ** unit ≡ fmap (λ a → (a , tt)) v
    law-right-identity v = begin
      v ** unit 
        ≡⟨⟩
      fmap (_,_) v <*> pure (tt)
        ≡⟨ cong (λ X → X <*> pure (tt)) (law-applicative-fmap _,_ v) ⟩
      pure (_,_) <*> v <*> pure (tt)
        ≡⟨ law-interchange (pure (_,_) <*> v) (tt) ⟩
      pure (λ f → f (tt)) <*> (pure (_,_) <*> v)
        ≡⟨ sym (law-composition (pure (λ f → f (tt))) (pure (_,_)) v) ⟩
      pure (_∘_) <*> pure (λ f → f (tt)) <*> pure (_,_) <*> v
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> v) (law-homomorphism (λ f → f (tt)) _∘_) ⟩
      pure (_∘_ (λ f → f (tt))) <*> pure (_,_) <*> v
        ≡⟨ cong (λ X → X <*> v) (law-homomorphism _,_ (_∘_ (λ f → f (tt)))) ⟩
      pure ((λ f → f (tt)) ∘ _,_) <*> v
        ≡⟨⟩
      pure (λ a → (a , tt)) <*> v
        ≡⟨ sym (law-applicative-fmap (λ a → (a , tt)) v) ⟩
      fmap (λ a → (a , tt)) v ∎
  
  abstract
    law-right-identity' : {i j : Ixs} {α : Type} → (v : F i j α) 
                        → fmap proj₁ (v ** unit) ≡ v
    law-right-identity' {i} {j} {α} v 
      = trans (cong (λ X → fmap proj₁ X) (law-right-identity v)) 
              (trans (cong (λ X → X v) (sym $ law-functor-compose i j proj₁ (λ a → a , tt))) 
                     (cong (λ X → X v) (law-functor-id i j))) 

  abstract
    law-associativity : {i j k l : Ixs} {α β γ : Type} → (u : F i j α) (v : F j k β) (w : F k l γ) 
                      → u ** (v ** w) ≡ fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) 
    law-associativity u v w = begin
      u ** (v ** w) 
        ≡⟨⟩ 
      fmap (_,_) u <*> (fmap (_,_) v <*> w) 
        ≡⟨ cong (λ X → X <*> (fmap (_,_) v <*> w)) (law-applicative-fmap _,_ u) ⟩ 
      pure (_,_) <*> u <*> (fmap (_,_) v <*> w) 
        ≡⟨ cong (λ X → pure (_,_) <*> u <*> (X <*> w)) (law-applicative-fmap _,_ v) ⟩ 
      pure (_,_) <*> u <*> (pure (_,_) <*> v <*> w) 
        ≡⟨ sym (law-composition (pure _,_ <*> u) (pure _,_ <*> v) w) ⟩ 
      pure _∘_ <*> (pure (_,_) <*> u) <*> (pure (_,_) <*> v) <*> w 
        ≡⟨ cong (λ X → X <*> (pure (_,_) <*> v) <*> w) (sym (law-composition (pure _∘_) (pure _,_) u)) ⟩ 
      pure _∘_ <*> pure _∘_ <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w 
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w) (law-homomorphism _∘_ _∘_) ⟩ 
      pure (_∘_ _∘_) <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w 
        ≡⟨ cong (λ X → X <*> u <*> (pure (_,_) <*> v) <*> w) (law-homomorphism _,_ (_∘_ _∘_)) ⟩ 
      pure (_∘_ ∘ _,_) <*> u <*> (pure (_,_) <*> v) <*> w 
        ≡⟨ cong (λ X → X <*> w) (sym (law-composition (pure (_∘_ ∘ _,_) <*> u) (pure _,_) v)) ⟩ 
      pure _∘_ <*> (pure (_∘_ ∘ _,_) <*> u) <*> pure (_,_) <*> v <*> w 
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> v <*> w) (sym (law-composition (pure _∘_) (pure (_∘_ ∘ _,_)) u)) ⟩ 
      pure _∘_ <*> pure _∘_ <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w 
        ≡⟨ cong (λ X → X <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w) (law-homomorphism _∘_ _∘_) ⟩ 
      pure (_∘_ _∘_) <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w 
        ≡⟨ cong (λ X → X <*> u <*> pure (_,_) <*> v <*> w) (law-homomorphism (_∘_ ∘ _,_) (_∘_ _∘_)) ⟩ 
      pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> pure (_,_) <*> v <*> w
        ≡⟨ cong (λ X → X <*> v <*> w) (law-interchange (pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u) _,_) ⟩ 
      pure (λ f → f _,_) <*> (pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u) <*> v <*> w
        ≡⟨ cong (λ X → X <*> v <*> w) (sym (law-composition (pure (λ f → f _,_)) (pure (_∘_ ∘ (_∘_ ∘ _,_))) u)) ⟩ 
      pure _∘_ <*> pure (λ f → f _,_) <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w
        ≡⟨ cong (λ X → X <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w) (law-homomorphism (λ f → f _,_) _∘_) ⟩ 
      pure (_∘_ (λ f → f _,_)) <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w
        ≡⟨ cong (λ X → X <*> u <*> v <*> w) (law-homomorphism (_∘_ ∘ (_∘_ ∘ _,_)) (_∘_ (λ f → f _,_))) ⟩ 
      pure ((λ f → f _,_) ∘ (_∘_ ∘ (_∘_ ∘ _,_))) <*> u <*> v <*> w
        ≡⟨ refl ⟩ -- Again, obvious...
      pure ((_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) ∘ _,_) <*> u <*> v <*> w
        ≡⟨ cong (λ X → X <*> u <*> v <*> w) (sym (law-homomorphism _,_ (_∘_ (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))))) ⟩ 
      pure (_∘_ (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))) <*> pure (_,_) <*> u <*> v <*> w
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> u <*> v <*> w) (sym (law-homomorphism (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) _∘_)) ⟩ 
      pure _∘_ <*> pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) <*> pure (_,_) <*> u <*> v <*> w
        ≡⟨ cong (λ X → X <*> v <*> w) (law-composition (pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))) (pure _,_) u) ⟩ 
      pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) <*> (pure (_,_) <*> u) <*> v <*> w
        ≡⟨ cong (λ X → X <*> (pure (_,_) <*> u) <*> v <*> w) (sym (law-homomorphism ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) _∘_)) ⟩ 
      pure _∘_ <*> pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) <*> (pure (_,_) <*> u) <*> v <*> w
        ≡⟨ cong (λ X → X <*> w) (law-composition (pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) (pure (_,_) <*> u) v) ⟩ 
      pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) <*> (pure (_,_) <*> u <*> v) <*> w
        ≡⟨ cong (λ X → X <*> (pure (_,_) <*> u <*> v) <*> w) (sym (law-homomorphism _,_ (_∘_ (_∘_ (λ {((a , b) , c) → (a , (b , c))}))))) ⟩ 
      pure (_∘_ (_∘_ (λ {((a , b) , c) → (a , (b , c))}))) <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w
        ≡⟨ cong (λ X → X <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w) (sym (law-homomorphism (_∘_ (λ {((a , b) , c) → (a , (b , c))})) _∘_)) ⟩ 
      pure _∘_ <*> pure (_∘_ (λ {((a , b) , c) → (a , (b , c))})) <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w
        ≡⟨ cong (λ X → X <*> w) (law-composition (pure (_∘_ (λ {((a , b) , c) → (a , (b , c))}))) (pure _,_) (pure (_,_) <*> u <*> v)) ⟩ 
      pure (_∘_ (λ {((a , b) , c) → (a , (b , c))})) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w
        ≡⟨ cong (λ X → X <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w) (sym (law-homomorphism (λ {((a , b) , c) → (a , (b , c))}) _∘_)) ⟩ 
      pure _∘_ <*> pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w
        ≡⟨ law-composition (pure (λ {((a , b) , c) → (a , (b , c))})) (pure _,_ <*> (pure (_,_) <*> u <*> v)) w ⟩ 
      pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w )
        ≡⟨ cong (λ X → pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (X <*> v) <*> w )) (sym (law-applicative-fmap _,_ u)) ⟩ 
      pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (fmap (_,_) u <*> v) <*> w )
        ≡⟨ cong (λ X → pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( X <*> w )) (sym (law-applicative-fmap _,_ (fmap (_,_) u <*> v))) ⟩ 
      pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( fmap _,_ (fmap (_,_) u <*> v) <*> w )
        ≡⟨⟩ 
      pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( (u ** v) ** w )
        ≡⟨ sym (law-applicative-fmap (λ {((a , b) , c) → (a , (b , c))}) ((u ** v) ** w)) ⟩ 
      fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) ∎


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

