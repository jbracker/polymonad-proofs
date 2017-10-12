 

open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ ) 
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ )

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym ; trans )
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to hask-functor-eq ) hiding ( functor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Indexed.Applicative
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
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

HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                                    → (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
                                                    ↔ (IndexedLaxMonoidalFunctor (Codisc Ixs) (SetMonCat {zero}) (SetMonCat {zero}))
HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor {ℓIxs} {Ixs} = bijection HaskellIndexedApplicative→IndexedLaxMonoidalFunctor IndexedLaxMonoidalFunctor→HaskellIndexedApplicative l→r→l r→l→r
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    SetMonCat' = SetMonCat {zero}
    
    abstract
      l→r→l : (b : IndexedLaxMonoidalFunctor (Codisc Ixs) (SetMonCat {zero}) (SetMonCat {zero})) 
            → HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative b) ≡ b
      l→r→l FMon = indexed-lax-monoidal-functor-eq F-eq (≡-to-≅ ε-eq) μ-eq
        where
          open Category
          open MonoidalCategory hiding ( Obj ; Hom )
          open IndexedLaxMonoidalFunctor renaming ( μ-natural-transformation to μ-nat )
          
          FMon' = HaskellIndexedApplicative→IndexedLaxMonoidalFunctor (IndexedLaxMonoidalFunctor→HaskellIndexedApplicative FMon)

          I = Codisc Ixs
          _∘I_ = Category._∘_ I
          
          F₀-eq : {i j : Ixs} → (f : CodiscreteArrow i j) → (α : Category.Obj SetCat) 
                → (Functor.F₀ (F FMon' f) α) ≡ Functor.F₀ (F FMon f) α
          F₀-eq f@(codisc i j) α = refl
          
          F₁-eq : {i j : Ixs} → (f : CodiscreteArrow i j) 
                → (λ {a b} → Functor.F₁ (F FMon' f) {a} {b}) ≅ (λ {a b} → Functor.F₁ (F FMon f) {a} {b})
          F₁-eq f@(codisc i j) = hrefl
          
          F-eq : (λ {i j} → F FMon' {i} {j}) ≡ F FMon
          F-eq = implicit-fun-ext 
               $ λ (i : Ixs) → implicit-fun-ext 
               $ λ (j : Ixs) → fun-ext 
               $ λ (f : CodiscreteArrow i j) → functor-eq (fun-ext $ λ (α : Category.Obj SetCat) → F₀-eq f α) (F₁-eq f)
          
          ε-eq : ε FMon' ≡ ε FMon
          ε-eq = fun-ext $ λ (i : Ixs) → begin
            ε FMon' i
              ≡⟨ refl ⟩
            (λ x → Functor.F₁ (F FMon (codisc i i)) (λ {(lift tt) → lift tt}) (ε FMon i x))
              ≡⟨ refl ⟩
            (λ x → Functor.F₁ (F FMon (codisc i i)) (λ x → x) (ε FMon i x))
              ≡⟨ fun-ext (λ x → cong (λ f → f (ε FMon i x)) (Functor.id (F FMon (codisc i i)))) ⟩
            ε FMon i ∎
          
          μ-eq : (λ {i j k} → μ-nat FMon' {i} {j} {k}) ≅ (λ {i j k} → μ-nat FMon {i} {j} {k})
          μ-eq = het-implicit-fun-ext (het-fun-ext hrefl $ λ (i : Ixs) → hcong (λ X → {j k : Ixs} (f : Hom (Codisc Ixs) i j) (g : Hom (Codisc Ixs) j k) 
                                                                                    → NaturalTransformation [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ] 
                                                                                                            [ X (g ∘I f) ]∘[ tensor SetMonCat ]) 
                                                                               (≡-to-≅ F-eq)) 
               $ λ (i : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (j : Ixs) → hcong (λ X → {k : Ixs} (f : Hom (Codisc Ixs) i j) (g : Hom (Codisc Ixs) j k) 
                                                                                                  → NaturalTransformation [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ] 
                                                                                                                          [ X (g ∘I f) ]∘[ tensor SetMonCat ]) 
                                                                                             (≡-to-≅ F-eq)) 
               $ λ (j : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (k : Ixs) → hcong (λ X → (f : Hom (Codisc Ixs) i j) (g : Hom (Codisc Ixs) j k) 
                                                                                                  → NaturalTransformation [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ]
                                                                                                                          [ X (g ∘I f) ]∘[ tensor SetMonCat ]) 
                                                                                             (≡-to-≅ F-eq)) 
               $ λ (k : Ixs) → het-fun-ext (het-fun-ext hrefl $ λ (f : CodiscreteArrow i j) → hcong (λ X → (a : CodiscreteArrow j k) 
                                                                                                         → NaturalTransformation [ tensor SetMonCat ]∘[ [ X f ]×[ X a ] ] [ X (a ∘I f) ]∘[ tensor SetMonCat ]) 
                                                                                                    (≡-to-≅ F-eq)) 
               $ λ { f@(codisc i j) → het-fun-ext (het-fun-ext hrefl $ λ (g : CodiscreteArrow j k) → hcong (λ X → NaturalTransformation [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ] 
                                                                                                                                                 [ X (g ∘I f) ]∘[ tensor SetMonCat ]) 
                                                                                                                    (≡-to-≅ F-eq)) 
               $ λ { g@(codisc j k) → het-natural-transformation-eq (cong (λ X → [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ]) F-eq) 
                                                                             (cong (λ X → [ X (g ∘I f) ]∘[ tensor SetMonCat ]) F-eq) 
               $ het-fun-ext (het-fun-ext hrefl $ λ a×b → hcong (λ X → Hom SetCat ([ [ tensor SetMonCat ]∘[ [ X f ]×[ X g ] ] ]₀ a×b) ([ [ X (g ∘I f) ]∘[ tensor SetMonCat ] ]₀ a×b)) (≡-to-≅ F-eq)) 
               $ λ {(α , β) → hbegin
                 μ FMon' f g α β
                   ≅⟨ hrefl ⟩
                 (Functor.F₁ (F FMon (g ∘I f)) (λ {(f , a) → f a})) ∘F (μ FMon f g (β → α × β) β) ∘F (Functor.F₁ (F FMon f) _,_ *** (λ x → x))
                   ≅⟨ ≡-to-≅ $ cong (λ X → (Functor.F₁ (F FMon (g ∘I f)) (λ {(f , a) → f a}) ∘F μ FMon f g (β → α × β) β ∘F (Functor.F₁ (F FMon f) _,_ *** X))) (sym $ Functor.id (F FMon g)) ⟩
                 (Functor.F₁ (F FMon (g ∘I f)) (λ {(f , a) → f a})) ∘F (μ FMon f g (β → α × β) β) ∘F (Functor.F₁ (F FMon f) _,_ *** Functor.F₁ (F FMon g) (λ (x : β) → x))
                   ≅⟨ ≡-to-≅ $ cong (λ X → (Functor.F₁ (F FMon (g ∘I f)) (λ { (f , a) → f a }) ∘F X)) (sym $ natural (μ-nat FMon f g)) ⟩
                 (Functor.F₁ (F FMon (g ∘I f)) (λ {(f , a) → f a}) ∘F Functor.F₁ (F FMon (g ∘I f)) (_,_ *** (λ x → x)) ∘F μ FMon f g α β)
                   ≅⟨ ≡-to-≅ $ cong (λ X → (X ∘F μ FMon f g α β)) (sym $ Functor.compose (F FMon (g ∘I f))) ⟩
                 (Functor.F₁ (F FMon (g ∘I f)) (λ x → x) ∘F μ FMon f g α β)
                   ≅⟨ ≡-to-≅ $ cong (λ X → (X ∘F μ FMon f g α β )) (Functor.id (F FMon (g ∘I f))) ⟩
                 μ FMon f g α β ∎h } } }
    
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
                                                    → (IndexedLaxMonoidalFunctor (Codisc Ixs) SetMonCat SetMonCat)
                                                    ↔ (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
IndexedLaxMonoidalFunctor↔HaskellIndexedApplicative = Bijection.sym HaskellIndexedApplicative↔IndexedLaxMonoidalFunctor
