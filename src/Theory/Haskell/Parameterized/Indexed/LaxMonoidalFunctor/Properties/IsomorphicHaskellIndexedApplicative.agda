 

open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( sym ; trans ; cong )
open ≡-Reasoning

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym ; trans )
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to hask-functor-eq ) hiding ( functor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Indexed.Applicative
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Equality
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.FromHaskellIndexedApplicative
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.ToHaskellIndexedApplicative

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.IsomorphicHaskellIndexedApplicative where

private
  Hask = setCategory {zero}

HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                                    → (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
                                                    ↔ (IndexedLaxMonoidalFunctor Ixs (SetMonCat {zero}) (SetMonCat {zero}))
HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor {ℓIxs} {Ixs} = bijection HaskellIndexedApplicative→IndexedLaxMonoidalFunctor IndexedLaxMonoidalFunctor→HaskellIndexedApplicative l→r→l r→l→r
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    abstract
      l→r→l : (b : IndexedLaxMonoidalFunctor Ixs (SetMonCat {zero}) (SetMonCat {zero})) 
            → HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative b) ≡ b
      l→r→l FMon = indexed-lax-monoidal-functor-eq (fun-ext $ λ i → fun-ext $ λ j → refl) (≡-to-≅ ε-eq) (≡-to-≅ μ-eq)
        where
          open IndexedLaxMonoidalFunctor renaming ( μ-natural-transformation to μ-nat )
          
          ε-eq : ε (HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative FMon)) ≡ ε FMon
          ε-eq = fun-ext $ λ (i : Ixs) → begin
            ε (HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative FMon)) i
              ≡⟨ refl ⟩
            (λ x → Functor.F₁ (F FMon i i) (λ {(lift tt) → lift tt}) (ε FMon i x))
              ≡⟨ refl ⟩
            (λ x → Functor.F₁ (F FMon i i) (λ x → x) (ε FMon i x))
              ≡⟨ fun-ext (λ x → cong (λ f → f (ε FMon i x)) (Functor.id (F FMon i i))) ⟩
            ε FMon i ∎
          
          μ-eq : μ-nat (HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative FMon)) ≡ μ-nat FMon
          μ-eq = fun-ext $ λ (i : Ixs) → fun-ext $ λ (j : Ixs) → fun-ext $ λ (k : Ixs) → natural-transformation-eq $ fun-ext $ λ {(α , β) → fun-ext $ λ {(fa , fb) → begin
            μ (HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative FMon)) i j k α β (fa , fb)
              ≡⟨ refl ⟩
            Functor.F₁ (F FMon i k) (λ {(f , a) → f a}) (μ FMon i j k (β → α × β) β (Functor.F₁ (F FMon i j) _,_ fa , fb))
              ≡⟨ refl ⟩
            Functor.F₁ (F FMon i k) (λ {(f , a) → f a}) (μ FMon i j k (β → α × β) β ((Functor.F₁ (F FMon i j) _,_ *** (λ x → x)) (fa , fb)))
              ≡⟨ cong (λ X → (Functor.F₁ (F FMon i k) (λ {(f , a) → f a}) ∘F μ FMon i j k (β → α × β) β ∘F (Functor.F₁ (F FMon i j) _,_ *** X)) (fa , fb) ) (sym $ Functor.id (F FMon j k)) ⟩
            (Functor.F₁ (F FMon i k) (λ {(f , a) → f a}) ∘F μ FMon i j k (β → α × β) β ∘F (Functor.F₁ (F FMon i j) _,_ *** Functor.F₁ (F FMon j k) (λ (x : β) → x)) ) (fa , fb)
              ≡⟨ cong (λ X → (Functor.F₁ (F FMon i k) (λ { (f , a) → f a }) ∘F X) (fa , fb)) (sym $ natural (μ-nat FMon i j k)) ⟩
            (Functor.F₁ (F FMon i k) (λ {(f , a) → f a}) ∘F Functor.F₁ (F FMon i k) (_,_ *** (λ x → x)) ∘F μ FMon i j k α β) (fa , fb)
              ≡⟨ cong (λ X → (X ∘F μ FMon i j k α β) (fa , fb)) (sym $ Functor.compose (F FMon i k)) ⟩
            (Functor.F₁ (F FMon i k) (λ x → x) ∘F μ FMon i j k α β) (fa , fb)
              ≡⟨ cong (λ X → (X ∘F μ FMon i j k α β ) (fa , fb)) (Functor.id (F FMon i k)) ⟩
            μ FMon i j k α β (fa , fb) ∎ } }
    
    abstract
      r→l→r : (a : Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs)) 
            → IndexedLaxMonoidalFunctor→HaskellIndexedApplicative (HaskellIndexedApplicative→IndexedLaxMonoidalFunctor a) ≡ a
      r→l→r (F' , applic) = Σ-eq refl $ ≡-to-≅ $ indexed-applicative-eq pure-eq ap-eq fun-eq
        where 
          open IndexedLaxMonoidalFunctor
          open IxApplicative applic
          
          abstract
            pure-eq : (λ {α} {i} a → IxApplicative.pure (proj₂ $ IndexedLaxMonoidalFunctor→HaskellIndexedApplicative $ HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (F' , applic)) {α} {i} a) ≡ pure
            pure-eq = implicit-fun-ext $ λ (α : Type) → implicit-fun-ext $ λ (i : Ixs) → fun-ext $ λ (a : α) → begin
              IxApplicative.pure (proj₂ $ IndexedLaxMonoidalFunctor→HaskellIndexedApplicative $ HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (F' , applic)) a
                ≡⟨⟩
              fmap (λ _ → a) unit
                ≡⟨ law-applicative-fmap (λ _ → a) unit ⟩
              (pure (λ _ → a)) <*> unit
                ≡⟨ law-homomorphism (lift tt) (λ _ → a) ⟩
              pure a ∎
          
          abstract
            ap-eq : (λ {α β} {i j k} f a → IxApplicative._<*>_ (proj₂ $ IndexedLaxMonoidalFunctor→HaskellIndexedApplicative $ HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (F' , applic)) {α} {β} {i} {j} {k} f a) ≡ _<*>_
            ap-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext $ λ f → fun-ext $ λ a → begin
              IxApplicative._<*>_ (proj₂ $ IndexedLaxMonoidalFunctor→HaskellIndexedApplicative $ HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (F' , applic)) f a 
                ≡⟨⟩
              fmap (λ {(f , a) → f a}) ((fmap _,_ f) <*> a)
                ≡⟨ law-applicative-fmap (λ {(f , a) → f a}) (fmap _,_ f <*> a) ⟩
              pure (λ {(f , a) → f a}) <*> ((fmap _,_ f) <*> a)
                ≡⟨ cong (λ X → pure (λ { (f , a) → f a }) <*> (X <*> a)) (law-applicative-fmap _,_ f) ⟩
              pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f <*> a)
                ≡⟨ sym (law-composition (pure (λ {(f , a) → f a})) (pure _,_ <*> f) a) ⟩
              pure _∘′_ <*> pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f) <*> a
                ≡⟨ cong (λ X → X <*> (pure _,_ <*> f) <*> a) (law-homomorphism (λ {(f , a) → f a}) _∘′_) ⟩
              pure (_∘′_ (λ {(f , a) → f a})) <*> (pure _,_ <*> f) <*> a
                ≡⟨ cong (λ X → X <*> a) (sym (law-composition (pure (_∘′_ (λ {(f , a) → f a}))) (pure _,_) f)) ⟩
              pure _∘′_ <*> pure (_∘′_ (λ {(f , a) → f a})) <*> pure _,_ <*> f <*> a
                ≡⟨ cong (λ X → X <*> pure _,_ <*> f <*> a) (law-homomorphism (_∘′_ (λ {(f , a) → f a})) _∘′_) ⟩
              pure (_∘′_ (_∘′_ (λ {(f , a) → f a}))) <*> pure _,_ <*> f <*> a
                ≡⟨ cong (λ X → X <*> f <*> a) (law-homomorphism _,_ (_∘′_ (_∘′_ (λ {(f , a) → f a})))) ⟩
              pure ((_∘′_ (λ {(f , a) → f a})) ∘′ _,_) <*> f <*> a
                ≡⟨⟩
              pure (λ x → x) <*> f <*> a
                ≡⟨ cong (λ X → _<*>_ X a) (law-id f) ⟩
              f <*> a ∎
          
          abstract
            fun-eq : IxApplicative.functor (proj₂ $ IndexedLaxMonoidalFunctor→HaskellIndexedApplicative $ HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (F' , applic)) ≡ IxApplicative.functor applic
            fun-eq = fun-ext $ λ i → fun-ext $ λ j → Haskell.Functor.functor-eq refl

          
IndexedLaxMonoidalFunctor↔HaskellIndexedApplicative : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                                    → (IndexedLaxMonoidalFunctor Ixs SetMonCat SetMonCat)
                                                    ↔ (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
IndexedLaxMonoidalFunctor↔HaskellIndexedApplicative = Bijection.sym HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor
