
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

open import Theory.Monoid

module Haskell.Parameterized.Graded.Applicative where

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

  private
    abstract
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
  
  abstract
    law-left-identity : {i : M} {α : Type} → (v : F i α) 
                      → unit ** v ≅ fmap (λ a → (lift tt , a)) v
    law-left-identity {i} {α} v = begin
      (F (ε ∙ i) (Lift ⊤ × α) ∋ (unit ** v))
        ≅⟨ refl ⟩
      (F (ε ∙ i) (Lift ⊤ × α) ∋ (fmap (_,_) (pure (lift tt)) <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ i) (Lift ⊤ × α) ∋ Y <*> v) (≡-to-≅ (sym left-id)) (law-applicative-fmap _,_ (pure (lift tt))) ⟩
      (F ((ε ∙ ε) ∙ i) (Lift ⊤ × α) ∋ (pure (_,_) <*> pure (lift tt) <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ i) (Lift ⊤ × α) ∋ Y <*> v) (≡-to-≅ left-id) (law-homomorphism (lift tt) _,_) ⟩
      (F (ε ∙ i) (Lift ⊤ × α) ∋ (pure (λ a → (lift tt , a)) <*> v))
        ≅⟨ hcong₂ (λ X Y → F X (Lift ⊤ × α) ∋ Y) (≡-to-≅ left-id) (hsym (law-applicative-fmap (λ a → (lift tt , a)) v)) ⟩
      (F i (Lift ⊤ × α) ∋ (fmap (λ a → (lift tt , a)) v)) ∎
  
  abstract
    law-left-identity' : {i : M} {α : Type} → (v : F i α) 
                       → fmap proj₂ (unit ** v) ≅ v
    law-left-identity' {i} {α} v = begin
      (F (ε ∙ i) α ∋ (fmap proj₂ (unit ** v)))
        ≅⟨ hcong₂ (λ X Y → F X α ∋ fmap proj₂ Y) (≡-to-≅ left-id) (law-left-identity v) ⟩
      (F i α ∋ (fmap proj₂ (fmap (λ a → (lift tt , a)) v)))
        ≅⟨ hcong (λ X → F i α ∋ X v) (≡-to-≅ (sym $ Functor.law-compose (functor i) proj₂ (λ a → lift tt , a))) ⟩
      (F i α ∋ (fmap (proj₂ {a = ℓ} ∘ (λ a → (lift tt , a))) v))
        ≅⟨ refl ⟩
      (F i α ∋ (fmap (λ x → x) v))
        ≅⟨ hcong (λ X → X v) (≡-to-≅ (Functor.law-id (functor i))) ⟩
      v ∎

  abstract
    law-right-identity : {i : M} {α : Type} → (v : F i α) 
                       → v ** unit ≅ fmap (λ a → (a , lift tt)) v
    law-right-identity {i} {α} v = begin
      v ** unit
        ≅⟨ refl ⟩
      (F (i ∙ ε) (α × Lift ⊤) ∋ (fmap _,_ v <*> pure (lift tt)))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ ε) (α × Lift ⊤) ∋ Y <*> pure (lift tt)) (≡-to-≅ (sym left-id)) (law-applicative-fmap _,_ v) ⟩
      (F ((ε ∙ i) ∙ ε) (α × Lift ⊤) ∋ (pure (_,_) <*> v <*> pure (lift tt)))
        ≅⟨ hcong₂ (λ X Y → F X (α × Lift ⊤) ∋ Y) (≡-to-≅ (trans right-id (sym left-id))) (law-interchange (pure (_,_) <*> v) (lift tt)) ⟩
      (F (ε ∙ (ε ∙ i)) (α × Lift ⊤) ∋ (pure (λ f → f (lift tt)) <*> (pure (_,_) <*> v)))
        ≅⟨ hcong₂ (λ X Y → F X (α × Lift ⊤) ∋ Y) (≡-to-≅ (trans (cong (λ Z → Z ∙ (ε ∙ i)) (sym left-id)) assoc)) (hsym (law-composition (pure (λ f → f (lift tt))) (pure (_,_)) v)) ⟩
      (F (((ε ∙ ε) ∙ ε) ∙ i) (α × Lift ⊤) ∋ (pure (_∘_) <*> pure (λ f → f (lift tt)) <*> pure (_,_) <*> v))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ ε) ∙ i) (α × Lift ⊤) ∋ Y <*> pure (_,_) <*> v) (≡-to-≅ left-id) (law-homomorphism (λ f → f (lift tt)) _∘_) ⟩
      (F ((ε ∙ ε) ∙ i) (α × Lift ⊤) ∋ (pure (_∘_ (λ f → f (lift tt))) <*> pure (_,_) <*> v))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ i) (α × Lift ⊤) ∋ Y <*> v) (≡-to-≅ left-id) (law-homomorphism _,_ (_∘_ (λ f → f (lift tt)))) ⟩
      (F (ε ∙ i) (α × Lift ⊤) ∋ (pure ((λ f → f (lift tt)) ∘ _,_) <*> v))
        ≅⟨ refl ⟩
      (F (ε ∙ i) (α × Lift ⊤) ∋ (pure (λ a → (a , lift tt)) <*> v))
        ≅⟨ hcong₂ (λ X Y → F X (α × Lift ⊤) ∋ Y) (≡-to-≅ left-id) (hsym (law-applicative-fmap (λ a → (a , lift tt)) v)) ⟩
      (F i (α × Lift ⊤) ∋ (fmap (λ a → (a , lift tt)) v)) ∎
  
  abstract
    law-right-identity' : {i : M} {α : Type} → (v : F i α) 
                        → fmap proj₁ (v ** unit) ≅ v
    law-right-identity' {i} {α} v = begin
      (F (i ∙ ε) α ∋ (fmap proj₁ (v ** unit)))
        ≅⟨ hcong₂ (λ X Y → F X α ∋ fmap proj₁ Y) (≡-to-≅ right-id) (law-right-identity v) ⟩
      (F i α ∋ (fmap proj₁ (fmap (λ a → (a , lift tt)) v)))
        ≅⟨ hcong (λ X → F i α ∋ X v) (≡-to-≅ (sym $ Functor.law-compose (functor i) proj₁ (λ a → (a , lift tt)))) ⟩
      (F i α ∋ (fmap (proj₁ {b = ℓ} ∘ (λ a → (a , lift tt))) v))
        ≅⟨ hcong (λ X → X v) (≡-to-≅ (Functor.law-id (functor i))) ⟩
      v ∎

  abstract
    law-associativity : {i j k : M} {α β γ : Type} → (u : F i α) (v : F j β) (w : F k γ) 
                      → u ** (v ** w) ≅ fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) 
    law-associativity {i} {j} {k} {α} {β} {γ} u v w = begin
      (F (i ∙ (j ∙ k)) (α × (β × γ)) ∋ (u ** (v ** w)))
        ≅⟨ refl ⟩ 
      (F (i ∙ (j ∙ k)) (α × (β × γ)) ∋ (fmap (_,_) u <*> (fmap (_,_) v <*> w)))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ (j ∙ k)) (α × (β × γ)) ∋ Y <*> (fmap (_,_) v <*> w)) (≡-to-≅ (sym left-id)) (law-applicative-fmap _,_ u) ⟩ 
      (F ((ε ∙ i) ∙ (j ∙ k)) (α × (β × γ)) ∋ ( pure (_,_) <*> u <*> (fmap (_,_) v <*> w)))
        ≅⟨ hcong₂ (λ X Y → F ((ε ∙ i) ∙ (X ∙ k)) (α × (β × γ)) ∋ pure (_,_) <*> u <*> (Y <*> w)) (≡-to-≅ (sym left-id)) (law-applicative-fmap _,_ v) ⟩ 
      (F ((ε ∙ i) ∙ ((ε ∙ j) ∙ k)) (α × (β × γ)) ∋ (pure (_,_) <*> u <*> (pure (_,_) <*> v <*> w)))
        ≅⟨ hcong₂ (λ X Y → F X (α × (β × γ)) ∋ Y) (≡-to-≅ (trans assoc (cong (λ X → (X ∙ (ε ∙ j)) ∙ k) (sym left-id)))) (hsym (law-composition (pure _,_ <*> u) (pure _,_ <*> v) w)) ⟩ 
      (F (((ε ∙ (ε ∙ i)) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> (pure (_,_) <*> u) <*> (pure (_,_) <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ Y <*> (pure (_,_) <*> v) <*> w)
                  (≡-to-≅ (trans assoc (cong (λ Z → (Z ∙ ε) ∙ i) (sym left-id))))
                  (hsym (law-composition (pure _∘_) (pure _,_) u)) ⟩ 
      (F (((((ε ∙ ε) ∙ ε) ∙ i) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure _∘_ <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((((X ∙ ε) ∙ i) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ Y <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w) (≡-to-≅ left-id) (law-homomorphism _∘_ _∘_) ⟩ 
      (F ((((ε ∙ ε) ∙ i) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ _∘_) <*> pure (_,_) <*> u <*> (pure (_,_) <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ i) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ Y <*> u <*> (pure (_,_) <*> v) <*> w) (≡-to-≅ left-id) (law-homomorphism _,_ (_∘_ _∘_)) ⟩ 
      (F (((ε ∙ i) ∙ (ε ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ ∘ _,_) <*> u <*> (pure (_,_) <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ k) (α × (β × γ)) ∋ Y <*> w) (≡-to-≅ (trans assoc (cong (λ Z → (Z ∙ ε) ∙ j) (sym left-id)))) (hsym (law-composition (pure (_∘_ ∘ _,_) <*> u) (pure _,_) v)) ⟩ 
      (F ((((ε ∙ (ε ∙ i)) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> (pure (_∘_ ∘ _,_) <*> u) <*> pure (_,_) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> pure (_,_) <*> v <*> w)
                  (≡-to-≅ (trans assoc (cong (λ Z → (Z ∙ ε) ∙ i) (sym left-id))))
                  (hsym (law-composition (pure _∘_) (pure (_∘_ ∘ _,_)) u)) ⟩ 
      (F ((((((ε ∙ ε) ∙ ε) ∙ i) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure _∘_ <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((((X ∙ ε) ∙ i) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w) (≡-to-≅ left-id) (law-homomorphism _∘_ _∘_) ⟩ 
      (F (((((ε ∙ ε) ∙ i) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ _∘_) <*> pure (_∘_ ∘ _,_) <*> u <*> pure (_,_) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((((X ∙ i) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> u <*> pure (_,_) <*> v <*> w) (≡-to-≅ left-id) (law-homomorphism (_∘_ ∘ _,_) (_∘_ _∘_)) ⟩ 
      (F ((((ε ∙ i) ∙ ε) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> pure (_,_) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> v <*> w) (≡-to-≅ (trans right-id (sym left-id))) (law-interchange (pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u) _,_) ⟩ 
      (F (((ε ∙ (ε ∙ i)) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure (λ f → f _,_) <*> (pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> v <*> w)
                  (≡-to-≅ (trans (cong (λ Z → Z ∙ (ε ∙ i)) (sym left-id)) assoc))
                  (hsym (law-composition (pure (λ f → f _,_)) (pure (_∘_ ∘ (_∘_ ∘ _,_))) u)) ⟩ 
      (F (((((ε ∙ ε) ∙ ε) ∙ i) ∙ j) ∙ k ) (α × (β × γ)) ∋ (pure _∘_ <*> pure (λ f → f _,_) <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((((X ∙ ε) ∙ i) ∙ j) ∙ k ) (α × (β × γ)) ∋ Y <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w) (≡-to-≅ left-id) (law-homomorphism (λ f → f _,_) _∘_) ⟩ 
      (F ((((ε ∙ ε) ∙ i) ∙ j) ∙ k ) (α × (β × γ)) ∋ (pure (_∘_ (λ f → f _,_)) <*> pure (_∘_ ∘ (_∘_ ∘ _,_)) <*> u <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> u <*> v <*> w) (≡-to-≅ left-id) (law-homomorphism (_∘_ ∘ (_∘_ ∘ _,_)) (_∘_ (λ f → f _,_))) ⟩
      (F (((ε ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure ((λ f → f _,_) ∘ (_∘_ ∘ (_∘_ ∘ _,_))) <*> u <*> v <*> w))
        ≅⟨ refl ⟩ -- Again, obvious...
      (F (((ε ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure ((_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) ∘ _,_) <*> u <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> u <*> v <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism _,_ (_∘_ (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))))) ⟩ 
      (F ((((ε ∙ ε) ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))) <*> pure (_,_) <*> u <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((((X ∙ ε) ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> pure (_,_) <*> u <*> v <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) _∘_)) ⟩ 
      (F (((((ε ∙ ε) ∙ ε) ∙ i) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) <*> pure (_,_) <*> u <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> v <*> w)
                  (≡-to-≅ (trans (sym assoc) (cong (λ Z → Z ∙ (ε ∙ i)) left-id)))
                  (law-composition (pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_))) (pure _,_) u) ⟩ 
      (F (((ε ∙ (ε ∙ i)) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) <*> (pure (_,_) <*> u) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ (ε ∙ i)) ∙ j) ∙ k) (α × (β × γ)) ∋ Y <*> (pure (_,_) <*> u) <*> v <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) _∘_)) ⟩ 
      (F ((((ε ∙ ε) ∙ (ε ∙ i)) ∙ j) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) <*> (pure (_,_) <*> u) <*> v <*> w))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ k) (α × (β × γ)) ∋ Y <*> w)
                  (≡-to-≅ (trans (cong (λ Z → (Z ∙ (ε ∙ i)) ∙ j) left-id) (sym assoc)))
                  (law-composition (pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_)) (pure (_,_) <*> u) v) ⟩ 
      (F ((ε ∙ ((ε ∙ i) ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure ((_∘_ (λ {((a , b) , c) → (a , (b , c))})) ∘ _,_) <*> (pure (_,_) <*> u <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ ((ε ∙ i) ∙ j)) ∙ k) (α × (β × γ)) ∋ Y <*> (pure (_,_) <*> u <*> v) <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism _,_ (_∘_ (_∘_ (λ {((a , b) , c) → (a , (b , c))}))))) ⟩ 
      (F (((ε ∙ ε) ∙ ((ε ∙ i) ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ (_∘_ (λ {((a , b) , c) → (a , (b , c))}))) <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε) ∙ ((ε ∙ i) ∙ j)) ∙ k) (α × (β × γ)) ∋ Y <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism (_∘_ (λ {((a , b) , c) → (a , (b , c))})) _∘_)) ⟩ 
      (F ((((ε ∙ ε) ∙ ε) ∙ ((ε ∙ i) ∙ j)) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure (_∘_ (λ {((a , b) , c) → (a , (b , c))})) <*> pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w))
        ≅⟨ hcong₂ (λ X Y → F (X ∙ k) (α × (β × γ)) ∋ Y <*> w)
                  (≡-to-≅ (trans (cong (λ Z → (Z ∙ ε) ∙ ((ε ∙ i) ∙ j)) left-id) (sym assoc)))
                  (law-composition (pure (_∘_ (λ {((a , b) , c) → (a , (b , c))}))) (pure _,_) (pure (_,_) <*> u <*> v)) ⟩ 
      (F ((ε ∙ (ε ∙ ((ε ∙ i) ∙ j))) ∙ k) (α × (β × γ)) ∋ (pure (_∘_ (λ {((a , b) , c) → (a , (b , c))})) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w))
        ≅⟨ hcong₂ (λ X Y → F ((X ∙ (ε ∙ ((ε ∙ i) ∙ j))) ∙ k) (α × (β × γ)) ∋ Y <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w)
                  (≡-to-≅ (sym left-id))
                  (hsym (law-homomorphism (λ {((a , b) , c) → (a , (b , c))}) _∘_)) ⟩ 
      (F (((ε ∙ ε) ∙ (ε ∙ ((ε ∙ i) ∙ j))) ∙ k) (α × (β × γ)) ∋ (pure _∘_ <*> pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) ) <*> w))
        ≅⟨ hcong₂ (λ X Y → F X (α × (β × γ)) ∋ Y)
                  (≡-to-≅ (trans (sym assoc) (cong (λ Z → Z ∙ ((ε ∙ ((ε ∙ i) ∙ j)) ∙ k)) left-id)))
                  (law-composition (pure (λ {((a , b) , c) → (a , (b , c))})) (pure _,_ <*> (pure (_,_) <*> u <*> v)) w) ⟩ 
      (F (ε ∙ ((ε ∙ ((ε ∙ i) ∙ j)) ∙ k)) (α × (β × γ)) ∋ (pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (pure (_,_) <*> u <*> v) <*> w )))
        ≅⟨ hcong₂ (λ X Y → F (ε ∙ ((ε ∙ (X ∙ j)) ∙ k)) (α × (β × γ)) ∋ pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (Y <*> v) <*> w ))
                  (≡-to-≅ left-id)
                  (hsym (law-applicative-fmap _,_ u)) ⟩ 
      (F (ε ∙ ((ε ∙ (i ∙ j)) ∙ k)) (α × (β × γ)) ∋ (pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( pure _,_ <*> (fmap (_,_) u <*> v) <*> w )))
        ≅⟨ hcong₂ (λ X Y → F (ε ∙ (X ∙ k)) (α × (β × γ)) ∋ pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( Y <*> w ))
                  (≡-to-≅ left-id)
                  (hsym (law-applicative-fmap _,_ (fmap (_,_) u <*> v))) ⟩ 
      (F (ε ∙ ((i ∙ j) ∙ k)) (α × (β × γ)) ∋ (pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( fmap _,_ (fmap (_,_) u <*> v) <*> w )))
        ≅⟨ refl ⟩ 
      (F (ε ∙ ((i ∙ j) ∙ k)) (α × (β × γ)) ∋ (pure (λ {((a , b) , c) → (a , (b , c))}) <*> ( (u ** v) ** w )))
        ≅⟨ hcong₂ (λ X Y → F X (α × β × γ) ∋ Y) (≡-to-≅ left-id) (hsym (law-applicative-fmap (λ {((a , b) , c) → (a , (b , c))}) ((u ** v) ** w))) ⟩ 
      (F ((i ∙ j) ∙ k) (α × (β × γ)) ∋ (fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ))) ∎

