
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

open import Theory.Monoid

module Haskell.Parameterized.Graded.Applicative where


_***_ : {ℓ : Level} {α β γ δ : Set ℓ} → (α → β) → (γ → δ) → ( (α × γ) → (β × δ) )
(f *** g) (a , b) = f a , g b

record GradedApplicative {ℓ : Level} {M : Set ℓ} (monoid : Monoid M) (F : M → TyCon) : Set (suc ℓ) where
  constructor graded-applicative
  infixl 5 _<*>_ _<$>_ _*>_ _<*_

  open Monoid monoid
  
  field
    pure : {α : Type} → α → F ε α
    _<*>_ : {i j : M} {α β : Type} → F i (α → β) → F j α → F (i ∙ j) β
    
    functor : (i : M) → Functor (F i)

  fmap : {i : M} {α β : Type} → (α → β) → F i α → F i β
  fmap {i} = Functor.fmap (functor i)

  _<$>_ = fmap
  
  field
    law-id : {i : M} {α : Type} 
           → (v : F i α) 
           → pure (λ x → x) <*> v ≅ v
    
    law-composition : {i j k : M} {α β γ : Type} 
                    → (u : F i (β → γ)) → (v : F j (α → β)) → (w : F k α) 
                    → (pure _∘_) <*> u <*> v <*> w ≅ u <*> (v <*> w)
    
    law-homomorphism : {α β : Type} 
                     → (x : α) → (f : α → β) 
                     → pure f <*> pure x ≅ pure (f x)
    
    law-interchange : {i : M} {α β : Type} 
                    → (u : F i (α → β)) → (x : α) 
                    → u <*> pure x ≅ pure (λ f → f x) <*> u
    
    law-applicative-fmap : {i : M} {α β : Type} 
                         → (f : α → β) → (x : F i α) 
                         → fmap f x ≅ pure f <*> x
  
  _*>_ : {i j : M} {α β : Type} → F i α → F j β → F (i ∙ j) β
  _*>_ {i} {j} {α} {β} u v = fmap (const (λ x → x)) u <*> v

  _<*_ : {i j : M} {α β : Type} → F i α → F j β → F (i ∙ j) α
  _<*_ {i} {j} {α} {β} u v = fmap (λ a b → a) u <*> v
  
  unit : F ε (Lift ⊤)
  unit = pure (lift tt)
  
  _**_ : {i j : M} {α β : Type} → F i α → F j β → F (i ∙ j) (α × β)
  _**_ u v = fmap (_,_) u <*> v

  p : {i j : M} {α β γ δ : Type} → (f : α → β) (g : γ → δ) (u : F i α) (v : F j γ)
    → (F (ε ∙ (i ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (fmap (_,_) u <*> v)))
    ≅ (F (ε ∙ ((ε ∙ i) ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (pure (_,_) <*> u <*> v)))
  p {i} {j} {α} {β} {γ} {δ} f g u v = hcong₂ (λ X Y  → (F (ε ∙ (X ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (Y <*> v)))) (≡-to-≅ $ sym left-id) (law-applicative-fmap _,_ u)
  

  abstract
    law-naturality : {i j : M} {α β γ δ : Type} → (f : α → β) (g : γ → δ) (u : F i α) (v : F j γ) 
                   → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
    law-naturality {i} {j} {α} {β} {γ} {δ} f g u v = ≅-to-≡ $ begin
      fmap (f *** g) (u ** v)
        ≅⟨ law-applicative-fmap (f *** g) (u ** v) ⟩
      (F (ε ∙ (i ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (fmap (_,_) u <*> v)))
        ≅⟨ hcong₂ (λ X Y  → (F (ε ∙ (X ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (Y <*> v)))) (≡-to-≅ $ sym left-id) (law-applicative-fmap _,_ u) ⟩
      (F (ε ∙ ((ε ∙ i) ∙ j)) (β × δ) ∋ (pure (f *** g) <*> (pure (_,_) <*> u <*> v)))
        ≅⟨ hcong₂ (λ X Y → F X (β × δ) ∋ Y) (≡-to-≅ (trans assoc (cong (λ Z → (Z ∙ (ε ∙ i)) ∙ j) (sym left-id)))) (hsym (law-composition (pure (f *** g)) (pure (_,_) <*> u) v)) ⟩
      (F (((ε ∙ ε) ∙ (ε ∙ i)) ∙ j) (β × δ) ∋ (pure (_∘_) <*> pure (f *** g) <*> (pure (_,_) <*> u) <*> v))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ (ε ∙ i)) ∙ j) (β × δ) ∋ (Y <*> (pure (_,_) <*> u) <*> v)) (≡-to-≅ left-id) (law-homomorphism (f *** g) _∘_) ⟩
      (F ((ε ∙ (ε ∙ i)) ∙ j) (β × δ) ∋ (pure (_∘_ (f *** g)) <*> (pure (_,_) <*> u) <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ j) (β × δ) ∋ _<*>_ Y v) (≡-to-≅ (trans assoc (cong (λ Z → (Z ∙ ε) ∙ i) (sym left-id)))) (hsym (law-composition (pure (_∘_ (f *** g))) (pure (_,_)) u)) ⟩
      (F ((((ε ∙ ε) ∙ ε) ∙ i) ∙ j) (β × δ) ∋ (pure (_∘_) <*> pure (_∘_ (f *** g)) <*> pure (_,_) <*> u <*> v ))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε) ∙ i) ∙ j) (β × δ) ∋ (Y <*> pure (_,_) <*> u <*> v)) (≡-to-≅ left-id) (law-homomorphism (_∘_ (f *** g)) _∘_) ⟩
      (F (((ε ∙ ε) ∙ i) ∙ j) (β × δ) ∋ (pure (_∘_ (_∘_ (f *** g))) <*> pure (_,_) <*> u <*> v))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ i) ∙ j) (β × δ) ∋ Y <*> u <*> v) (≡-to-≅ left-id) (law-homomorphism _,_ (_∘_ (_∘_ (f *** g)))) ⟩
      (F ((ε ∙ i) ∙ j) (β × δ) ∋ (pure ((_∘_ (f *** g)) ∘ (_,_)) <*> u <*> v ))
        ≅⟨ refl ⟩ -- Of course, how obvious...
      (F ((ε ∙ i) ∙ j) (β × δ) ∋ (pure (_∘_ (λ h → h g) ((_∘_) ∘ ((_,_) ∘ f))) <*> u <*> v))
        ≅⟨ hcong₂ (λ X Y → (F ((X ∙ i) ∙ j) (β × δ) ∋ Y <*> u <*> v)) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism ((_∘_) ∘ ((_,_) ∘ f)) (_∘_ (λ h → h g)))) ⟩
      (F (((ε ∙ ε) ∙ i) ∙ j) (β × δ) ∋ (pure (_∘_ (λ h → h g)) <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε) ∙ i) ∙ j) (β × δ) ∋ Y <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism (λ h → h g) _∘_)) ⟩
      (F ((((ε ∙ ε) ∙ ε) ∙ i) ∙ j) (β × δ) ∋ (pure (_∘_) <*> pure (λ h → h g) <*> pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ j) (β × δ) ∋ Y <*> v) (≡-to-≅ (trans (cong (λ Z → (Z ∙ ε) ∙ i) left-id) (sym assoc))) (law-composition (pure (λ h → h g)) (pure ((_∘_) ∘ ((_,_) ∘ f))) u) ⟩
      (F ((ε ∙ (ε ∙ i)) ∙ j) (β × δ) ∋ (pure (λ h → h g) <*> (pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u) <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ j) (β × δ) ∋ Y <*> v) (≡-to-≅ (trans left-id (sym right-id))) (hsym (law-interchange (pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u) g)) ⟩
      (F (((ε ∙ i) ∙ ε) ∙ j) (β × δ) ∋ (pure ((_∘_) ∘ ((_,_) ∘ f)) <*> u <*> pure g <*> v))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ i) ∙ ε) ∙ j) (β × δ) ∋ Y <*> u <*> pure g <*> v) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism ((_,_) ∘ f) (_∘_ (_∘_)))) ⟩
      (F ((((ε ∙ ε) ∙ i) ∙ ε) ∙ j) (β × δ) ∋ (pure (_∘_ (_∘_)) <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v))
        ≅⟨ hcong₂ (λ X Y → F ((((X ∙ ε) ∙ i) ∙ ε) ∙ j) (β × δ) ∋ Y <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism _∘_ _∘_)) ⟩
      (F (((((ε ∙ ε) ∙ ε) ∙ i) ∙ ε) ∙ j) (β × δ) ∋ (pure (_∘_) <*> pure (_∘_) <*> pure ((_,_) ∘ f) <*> u <*> pure g <*> v))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ ε) ∙ j) (β × δ) ∋ Y <*> pure g <*> v) (≡-to-≅ $ trans (cong (λ Z → (Z ∙ ε) ∙ i) left-id) (sym assoc)) (law-composition (pure (_∘_)) (pure (_,_ ∘ f)) u) ⟩
      (F (((ε ∙ (ε ∙ i)) ∙ ε) ∙ j) (β × δ) ∋ (pure (_∘_) <*> (pure (_,_ ∘ f) <*> u) <*> pure g <*> v))
        ≅⟨ hcong₂ (λ X Y → F X (β × δ) ∋ Y) (≡-to-≅ (trans (sym assoc) (cong (λ Z → Z ∙ (ε ∙ j)) left-id))) (law-composition (pure ((_,_) ∘ f) <*> u) (pure g) v) ⟩
      (F ((ε ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ (pure ((_,_) ∘ f) <*> u <*> (pure g <*> v)))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ Y <*> u <*> (pure g <*> v)) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism f (_∘_ (_,_)))) ⟩
      (F (((ε ∙ ε) ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ (pure (_∘_ (_,_)) <*> pure f <*> u <*> (pure g <*> v)))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε) ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ Y <*> pure f <*> u <*> (pure g <*> v)) (≡-to-≅ (sym left-id)) (hsym (law-homomorphism _,_ _∘_)) ⟩
      (F ((((ε ∙ ε) ∙ ε) ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ (pure (_∘_) <*> pure (_,_) <*> pure f <*> u <*> (pure g <*> v)))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ (ε ∙ j)) (β × δ) ∋ Y <*> (pure g <*> v)) (≡-to-≅ (trans (cong (λ Z → Z ∙ i) right-id) (sym assoc))) (law-composition (pure (_,_)) (pure f) u) ⟩
      (F ((ε ∙ (ε ∙ i)) ∙ (ε ∙ j)) (β × δ) ∋ (pure (_,_) <*> (pure f <*> u) <*> (pure g <*> v)))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ (ε ∙ j)) (β × δ) ∋ Y <*> (pure g <*> v)) (≡-to-≅ left-id) (hsym (law-applicative-fmap _,_ (pure f <*> u))) ⟩
      (F ((ε ∙ i) ∙ (ε ∙ j)) (β × δ) ∋ (fmap _,_ (pure f <*> u) <*> (pure g <*> v)))
        ≅⟨ hcong₂ (λ X Y → F ((ε ∙ i) ∙ X) (β × δ) ∋ fmap _,_ (pure f <*> u) <*> Y) (≡-to-≅ left-id) (hsym (law-applicative-fmap g v)) ⟩
      (F ((ε ∙ i) ∙ j) (β × δ) ∋ (fmap _,_ (pure f <*> u) <*> fmap g v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ j) (β × δ) ∋ fmap _,_ Y <*> fmap g v) (≡-to-≅ left-id) (hsym (law-applicative-fmap f u)) ⟩
      (F (i ∙ j) (β × δ) ∋ (fmap _,_ (fmap f u) <*> fmap g v))
        ≅⟨ refl ⟩
      (F (i ∙ j) (β × δ) ∋ (fmap f u ** fmap g v)) ∎
  
  {-
  
  abstract
    law-left-identity : {α : Type} → (v : F α) 
                      → unit ** v ≡ fmap (λ a → (lift tt , a)) v
    law-left-identity v = begin
      unit ** v 
        ≡⟨⟩
      fmap (_,_) (pure (lift tt)) <*> v 
        ≡⟨ cong (λ X → X <*> v) (law-applicative-fmap _,_ (pure (lift tt))) ⟩
      pure (_,_) <*> pure (lift tt) <*> v 
        ≡⟨ cong (λ X → X <*> v) (law-homomorphism (lift tt) _,_) ⟩
      pure (λ a → (lift tt , a)) <*> v
        ≡⟨ sym (law-applicative-fmap (λ a → (lift tt , a)) v) ⟩
      fmap (λ a → (lift tt , a)) v ∎
    
  abstract
    law-left-identity' : {α : Type} → (v : F α) 
                       → fmap proj₂ (unit ** v) ≡ v
    law-left-identity' {α} v = trans (cong (λ X → fmap proj₂ X) (law-left-identity v)) 
                                     (trans (cong (λ X → X v) (sym $ law-compose proj₂ (λ a → lift tt , a))) 
                                            (cong (λ X → X v) law-functor-id)) 
  
  abstract
    law-right-identity : {α : Type} → (v : F α) 
                       → v ** unit ≡ fmap (λ a → (a , lift tt)) v
    law-right-identity v = begin
      v ** unit 
        ≡⟨⟩
      fmap (_,_) v <*> pure (lift tt)
        ≡⟨ cong (λ X → X <*> pure (lift tt)) (law-applicative-fmap _,_ v) ⟩
      pure (_,_) <*> v <*> pure (lift tt)
        ≡⟨ law-interchange (pure (_,_) <*> v) (lift tt) ⟩
      pure (λ f → f (lift tt)) <*> (pure (_,_) <*> v)
        ≡⟨ sym (law-composition (pure (λ f → f (lift tt))) (pure (_,_)) v) ⟩
      pure (_∘_) <*> pure (λ f → f (lift tt)) <*> pure (_,_) <*> v
        ≡⟨ cong (λ X → X <*> pure (_,_) <*> v) (law-homomorphism (λ f → f (lift tt)) _∘_) ⟩
      pure (_∘_ (λ f → f (lift tt))) <*> pure (_,_) <*> v
        ≡⟨ cong (λ X → X <*> v) (law-homomorphism _,_ (_∘_ (λ f → f (lift tt)))) ⟩
      pure ((λ f → f (lift tt)) ∘ _,_) <*> v
        ≡⟨⟩
      pure (λ a → (a , lift tt)) <*> v
        ≡⟨ sym (law-applicative-fmap (λ a → (a , lift tt)) v) ⟩
      fmap (λ a → (a , lift tt)) v ∎
  
  abstract
    law-right-identity' : {α : Type} → (v : F α) 
                        → fmap proj₁ (v ** unit) ≡ v
    law-right-identity' {α} v = trans (cong (λ X → fmap proj₁ X) (law-right-identity v)) 
                                      (trans (cong (λ X → X v) (sym $ law-compose proj₁ (λ a → a , lift tt))) 
                                             (cong (λ X → X v) law-functor-id)) 

  abstract
    law-associativity : {α β γ : Type} → (u : F α) (v : F β) (w : F γ) 
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
