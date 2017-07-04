
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ( cong ; sym )
open import Relation.Binary.HeterogeneousEquality 
open ≅-Reasoning

open import Extensionality
open import Equality
open import Bijection hiding ( refl ; sym )

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative

open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation

open import Theory.Functor.Monoidal.Properties.FromHaskellApplicative
open import Theory.Functor.Monoidal.Properties.ToHaskellApplicative

module Theory.Functor.Monoidal.Properties.IsomorphicHaskellApplicative where 

open NaturalTransformation renaming ( η to nat-η )

HaskellApplicative↔LaxMonoidalFunctor : Σ TyCon Applicative ↔ LaxMonoidalFunctor (setMonoidalCategory {zero}) (setMonoidalCategory {zero})
HaskellApplicative↔LaxMonoidalFunctor = bijection l→r r→l r→l→r l→r→l
  where
    MonHask = setMonoidalCategory {zero}
    
    l→r : Σ TyCon Applicative → LaxMonoidalFunctor MonHask MonHask
    l→r (F , applic) = HaskellApplicative→LaxMonoidalFunctor applic
    
    r→l : LaxMonoidalFunctor MonHask MonHask → Σ TyCon Applicative
    r→l FMon = LaxMonoidalFunctor.F₀ FMon , LaxMonoidalFunctor→HaskellApplicative FMon
    
    abstract
      r→l→r : (b : LaxMonoidalFunctor setMonoidalCategory setMonoidalCategory) → l→r (r→l b) ≡ b
      r→l→r FMon = lax-monoidal-functor-eq refl ε-eq μ-eq
        where
          open LaxMonoidalFunctor FMon
          abstract
            ε-eq : LaxMonoidalFunctor.ε (l→r $ r→l FMon) ≅ LaxMonoidalFunctor.ε FMon
            ε-eq = begin
              LaxMonoidalFunctor.ε (l→r $ r→l FMon)
                ≡⟨⟩
              (λ _ → F₁ (λ _ → lift tt) (ε (lift tt)))
                ≅⟨ het-fun-ext refl (λ _ → cong (λ X → X (ε (lift tt))) (≡-to-≅ $ Functor.id F)) ⟩
              LaxMonoidalFunctor.ε FMon ∎
            
          abstract
            μ-eq : LaxMonoidalFunctor.μ-natural-transformation (l→r $ r→l FMon) ≅ μ-natural-transformation
            μ-eq = het-natural-transformation-eq refl refl $ het-fun-ext refl (λ {(α , β) → het-fun-ext refl (λ {(Fα , Fβ) → begin
              nat-η (LaxMonoidalFunctor.μ-natural-transformation (l→r $ r→l FMon)) (α , β) (Fα , Fβ)
                ≡⟨⟩
              (F₁ (λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((β → α × β) , β) ) (F₁ _,_ Fα , Fβ)
                ≡⟨⟩
              (F₁ (λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((β → α × β) , β) ∘F (F₁ _,_ *** (λ (x : F₀ β) → x)) ) (Fα , Fβ)
                ≅⟨ cong (λ X → (F₁ (λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((β → α × β) , β) ∘F (F₁ _,_ *** X)) (Fα , Fβ) ) (sym (≡-to-≅ (Functor.id F))) ⟩
              (F₁ (λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((β → α × β) , β) ∘F (F₁ _,_ *** F₁ (λ (x : β) → x)) ) (Fα , Fβ)
                ≅⟨ cong (λ X → (F₁ (λ { (f , a) → f a }) ∘F X) (Fα , Fβ)) (sym $ ≡-to-≅ $ natural μ-natural-transformation) ⟩
              (F₁ (λ {(f , a) → f a}) ∘F F₁ (_,_ *** (λ (x : β) → x)) ∘F nat-η μ-natural-transformation (α , β) ) (Fα , Fβ)
                ≅⟨ cong (λ X → (X ∘F nat-η μ-natural-transformation (α , β)) (Fα , Fβ)) (sym $ ≡-to-≅ $ Functor.compose F) ⟩
              (F₁ idF ∘F nat-η μ-natural-transformation (α , β) ) (Fα , Fβ)
                ≅⟨ cong (λ X → (X ∘F nat-η μ-natural-transformation (α , β) ) (Fα , Fβ)) (≡-to-≅ $ Functor.id F) ⟩
              nat-η μ-natural-transformation (α , β) (Fα , Fβ) ∎ }) })
    
    abstract
      l→r→l : (a : Σ TyCon Applicative) → r→l (l→r a) ≡ a
      l→r→l (F , applic) = Σ-eq refl $ ≡-to-≅ $ applicative-eq pure-eq ap-eq fun-eq
        where
          open LaxMonoidalFunctor renaming ( F to MonFunctor )
          open Applicative applic
          
          abstract
            pure-eq : (λ {α} a → Applicative.pure (proj₂ $ r→l $ l→r (F , applic)) {α} a) ≡ pure
            pure-eq = implicit-fun-ext $ λ (α : Type) → fun-ext $ λ (a : α) → ≅-to-≡ $ begin
              Applicative.pure (proj₂ $ r→l $ l→r (F , applic)) a
                ≡⟨⟩
              fmap (λ _ → a) unit
                ≅⟨ ≡-to-≅ (law-applicative-fmap (λ _ → a) unit) ⟩
              (pure (λ _ → a)) <*> unit
                ≅⟨ ≡-to-≅ (law-homomorphism (lift tt) (λ _ → a)) ⟩
              pure a ∎
            
          abstract
            ap-eq : (λ {α β} f a → Applicative._<*>_ (proj₂ $ r→l $ l→r (F , applic)) {α} {β} f a) ≡ _<*>_
            ap-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → fun-ext $ λ f → fun-ext $ λ a → ≅-to-≡ $ begin
              Applicative._<*>_ (proj₂ $ r→l $ l→r (F , applic)) f a 
                ≡⟨⟩
              fmap (λ {(f , a) → f a}) ((fmap _,_ f) <*> a)
                ≅⟨ ≡-to-≅ (law-applicative-fmap (λ {(f , a) → f a}) (fmap _,_ f <*> a)) ⟩
              pure (λ {(f , a) → f a}) <*> ((fmap _,_ f) <*> a)
                ≅⟨ cong (λ X → pure (λ { (f , a) → f a }) <*> (X <*> a)) 
                        (≡-to-≅ $ law-applicative-fmap _,_ f) ⟩
              pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f <*> a)
                ≅⟨ sym (≡-to-≅ (law-composition (pure (λ {(f , a) → f a})) (pure _,_ <*> f) a)) ⟩
              pure _∘′_ <*> pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f) <*> a
                ≅⟨ cong (λ X → X <*> (pure _,_ <*> f) <*> a) (≡-to-≅ (law-homomorphism (λ {(f , a) → f a}) _∘′_)) ⟩
              pure (_∘′_ (λ {(f , a) → f a})) <*> (pure _,_ <*> f) <*> a
                ≅⟨ cong (λ X → X <*> a) (sym (≡-to-≅ (law-composition (pure (_∘′_ (λ {(f , a) → f a}))) (pure _,_) f))) ⟩
              pure _∘′_ <*> pure (_∘′_ (λ {(f , a) → f a})) <*> pure _,_ <*> f <*> a
                ≅⟨ cong (λ X → X <*> pure _,_ <*> f <*> a) (≡-to-≅ (law-homomorphism (_∘′_ (λ {(f , a) → f a})) _∘′_)) ⟩
              pure (_∘′_ (_∘′_ (λ {(f , a) → f a}))) <*> pure _,_ <*> f <*> a
                ≅⟨ cong (λ X → X <*> f <*> a) (≡-to-≅ (law-homomorphism _,_ (_∘′_ (_∘′_ (λ {(f , a) → f a}))))) ⟩
              pure ((_∘′_ (λ {(f , a) → f a})) ∘′ _,_) <*> f <*> a
                ≡⟨⟩
              pure (λ x → x) <*> f <*> a
                ≅⟨ cong (λ X → _<*>_ X a) (≡-to-≅ $ law-id f) ⟩
              f <*> a ∎
            
          abstract
            fun-eq : Applicative.functor (proj₂ $ r→l $ l→r (F , applic)) ≡ Applicative.functor applic
            fun-eq = Haskell.Functor.functor-eq refl

