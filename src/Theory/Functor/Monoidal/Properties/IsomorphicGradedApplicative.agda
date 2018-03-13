
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; cong₂ to hcong₂ ; sym to hsym ; trans to htrans )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h ) 

open import Extensionality
open import Equality
open import Bijection hiding ( refl ; trans ) renaming ( sym to bsym )

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Graded.Applicative
open import Haskell.Parameterized.Graded.Applicative.Equality

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Examples.Discrete
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation

open import Theory.Functor.Monoidal.Properties.FromGradedApplicative
open import Theory.Functor.Monoidal.Properties.ToGradedApplicative

module Theory.Functor.Monoidal.Properties.IsomorphicGradedApplicative where 

open NaturalTransformation renaming ( η to nat-η )

GradedApplicative↔LaxMonoidalFunctor
  : {ℓ : Level} → {M : Set ℓ} → (mon : Monoid M)
  → Σ (M → TyCon) (GradedApplicative mon) ↔ LaxMonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {zero}) (setMonoidalCategory {zero})
GradedApplicative↔LaxMonoidalFunctor {ℓ} {M} mon = bijection l→r r→l r→l→r l→r→l
  where
    MonMonCat = monoidMonoidalCategory mon
    MonCat = discreteCategory M
    
    SetMonCat = setMonoidalCategory {zero}
    SetCat = setCategory {zero}
    
    l→r : Σ (M → TyCon) (GradedApplicative mon) → LaxMonoidalFunctor (MonMonCat ×CMon SetMonCat) SetMonCat
    l→r (F , applic) = GradedApplicative→LaxMonoidalFunctor applic
    
    r→l : LaxMonoidalFunctor (MonMonCat ×CMon SetMonCat) SetMonCat → Σ (M → TyCon) (GradedApplicative mon)
    r→l FMon = (λ i α → Functor.F₀ (LaxMonoidalFunctor.F FMon) (i , α)) , (LaxMonoidalFunctor→GradedApplicative FMon)
    
    abstract
      r→l→r : (b : LaxMonoidalFunctor (MonMonCat ×CMon SetMonCat) SetMonCat) → l→r (r→l b) ≡ b
      r→l→r FMon = lax-monoidal-functor-eq F-eq ε-eq μ-eq
        where
          open LaxMonoidalFunctor FMon
          open Category
          abstract
            F-eq : LaxMonoidalFunctor.F (l→r (r→l FMon)) ≡ F
            F-eq = Theory.Functor.Definition.functor-eq refl F₁-eq
              where
                F₁-eq' : (i j : M) (α β : Obj SetCat) (p : i ≡ j) (f : Hom SetCat α β)
                       → (x : LaxMonoidalFunctor.F₀ FMon (i , α))
                       → LaxMonoidalFunctor.F₁ (l→r (r→l FMon)) {i , α} {j , β} (p , f) x ≡ LaxMonoidalFunctor.F₁ FMon {i , α} {j , β} (p , f) x
                F₁-eq' i .i α β refl f x = refl
                
                F₁-eq : (λ {a b} → LaxMonoidalFunctor.F₁ (l→r (r→l FMon)) {a} {b}) ≅ (λ {a b} → LaxMonoidalFunctor.F₁ FMon {a} {b})
                F₁-eq = ≡-to-≅ $ implicit-fun-ext $ λ {(i , α) → implicit-fun-ext $ λ {(j , β) → fun-ext $ λ {(p , f) → fun-ext $ λ x → F₁-eq' i j α β p f x}}}
          
          abstract
            ε-eq : LaxMonoidalFunctor.ε (l→r $ r→l FMon) ≅ LaxMonoidalFunctor.ε FMon
            ε-eq = het-fun-ext refl (λ {(lift tt) → ≡-to-≅ $ cong (λ X → X (ε (lift tt))) (Functor.id F)})
            
          abstract
            μ-eq : LaxMonoidalFunctor.μ-natural-transformation (l→r $ r→l FMon) ≅ μ-natural-transformation
            μ-eq = het-natural-transformation-eq F-eq' G-eq η-eq
              where
                abstract
                  F-eq' : [ MonoidalCategory.tensor SetMonCat ]∘[ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]×[ LaxMonoidalFunctor.F (l→r $ r→l FMon) ] ]
                        ≡ [ MonoidalCategory.tensor SetMonCat ]∘[ [ F ]×[ F ] ]
                  F-eq' = Theory.Functor.Definition.functor-eq refl
                        $ het-implicit-fun-ext refl
                        $ (λ {((i₀ , α₀) , (i₁ , α₁)) → het-implicit-fun-ext refl
                        $ (λ {((j₀ , β₀) , (j₁ , β₁)) → het-fun-ext refl
                        $ (λ {((p , f) , (q , g)) → het-fun-ext refl
                        $ (λ x → ≡-to-≅ $ F₁-eq i₀ i₁ j₀ j₁ α₀ α₁ β₀ β₁ p q f g (proj₁ x) (proj₂ x)) }) }) })
                    where 
                      F₁-eq : (i₀ i₁ j₀ j₁ : M) (α₀ α₁ β₀ β₁ : Type) (p : i₀ ≡ j₀) (q : i₁ ≡ j₁) (f : α₀ → β₀) (g : α₁ → β₁)
                            → (x : proj₁ ([ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]×[ LaxMonoidalFunctor.F (l→r $ r→l FMon) ] ]₀ ((i₀ , α₀) , (i₁ , α₁))))
                            → (y : proj₂ ([ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]×[ LaxMonoidalFunctor.F (l→r $ r→l FMon) ] ]₀ ((i₀ , α₀) , (i₁ , α₁))))
                            → [ [ MonoidalCategory.tensor SetMonCat ]∘[ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]×[ LaxMonoidalFunctor.F (l→r $ r→l FMon) ] ] ]₁ ((p , f) , (q , g)) (x , y)
                            ≡ [ [ MonoidalCategory.tensor SetMonCat ]∘[ [ F ]×[ F ] ] ]₁ ((p , f) , (q , g)) (x , y)
                      F₁-eq i j .i .j _ _ _ _ refl refl f g x y = refl

                abstract
                  G-eq : [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]∘[ MonoidalCategory.tensor (MonMonCat ×CMon SetMonCat) ]
                       ≡ [ F ]∘[ MonoidalCategory.tensor (MonMonCat ×CMon SetMonCat) ]
                  G-eq = Theory.Functor.Definition.functor-eq refl
                        $ het-implicit-fun-ext refl
                        $ (λ {((i₀ , α₀) , (i₁ , α₁)) → het-implicit-fun-ext refl
                        $ (λ {((j₀ , β₀) , (j₁ , β₁)) → het-fun-ext refl
                        $ (λ {((p , f) , (q , g)) → het-fun-ext refl
                        $ (λ {x → ≡-to-≅ $ G₁-eq i₀ i₁ j₀ j₁ α₀ α₁ β₀ β₁ p q f g x }) }) }) })
                    where 
                      G₁-eq : (i₀ i₁ j₀ j₁ : M) (α₀ α₁ β₀ β₁ : Type) (p : i₀ ≡ j₀) (q : i₁ ≡ j₁) (f : α₀ → β₀) (g : α₁ → β₁)
                            → (x : [ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]∘[ MonoidalCategory.tensor (MonMonCat ×CMon SetMonCat) ] ]₀ ((i₀ , α₀) , (i₁ , α₁)))
                            → [ [ LaxMonoidalFunctor.F (l→r $ r→l FMon) ]∘[ MonoidalCategory.tensor (MonMonCat ×CMon SetMonCat) ] ]₁ ((p , f) , (q , g)) x
                            ≡ [ [ F ]∘[ MonoidalCategory.tensor (MonMonCat ×CMon SetMonCat) ] ]₁ ((p , f) , (q , g)) x
                      G₁-eq i j .i .j _ _ _ _ refl refl f g x = refl

                abstract
                  η-eq : nat-η (LaxMonoidalFunctor.μ-natural-transformation (l→r $ r→l FMon)) ≅ nat-η μ-natural-transformation
                  η-eq = het-fun-ext refl (λ {((i , α) , (j , β)) → het-fun-ext refl (λ { (Fα , Fβ) → hbegin
                    nat-η (LaxMonoidalFunctor.μ-natural-transformation (l→r $ r→l FMon)) ((i , α) , (j , β)) (Fα , Fβ)
                      ≅⟨ refl ⟩
                    (F₁ (refl , λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((i , (β → α × β)) , (j , β)) ) (F₁ (refl , _,_) Fα , Fβ)
                      ≅⟨ refl ⟩
                    (F₁ (refl , λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((i , (β → α × β)) , (j , β)) ∘F (F₁ (refl , _,_) *** (λ (x : F₀ (j , β)) → x)) ) (Fα , Fβ)
                      ≅⟨ hcong (λ X → (F₁ (refl , λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((i , (β → α × β)) , (j , β)) ∘F (F₁ (refl , _,_) *** X)) (Fα , Fβ) )
                               (hsym (≡-to-≅ (Functor.id F))) ⟩
                    (F₁ (refl , λ {(f , a) → f a}) ∘F nat-η μ-natural-transformation ((i , (β → α × β)) , (j , β)) ∘F (F₁ (refl , _,_) *** F₁ (refl , λ (x : β) → x)) ) (Fα , Fβ)
                      ≅⟨ hcong (λ X → (F₁ (refl , λ { (f , a) → f a }) ∘F X) (Fα , Fβ)) (hsym $ ≡-to-≅ $ natural μ-natural-transformation) ⟩
                    (F₁ (refl , λ {(f , a) → f a}) ∘F F₁ (refl , (_,_ *** (λ (x : β) → x))) ∘F nat-η μ-natural-transformation ((i , α) , (j , β)) ) (Fα , Fβ)
                      ≅⟨ hcong (λ X → (X ∘F nat-η μ-natural-transformation ((i , α) , (j , β))) (Fα , Fβ)) (hsym $ ≡-to-≅ $ Functor.compose F) ⟩
                    (F₁ (refl , λ x → x) ∘F nat-η μ-natural-transformation ((i , α) , (j , β)) ) (Fα , Fβ)
                      ≅⟨ hcong (λ X → (X ∘F nat-η μ-natural-transformation ((i , α) , (j , β)) ) (Fα , Fβ)) (≡-to-≅ $ Functor.id F) ⟩
                    (nat-η μ-natural-transformation ((i , α) , (j , β)) (Fα , Fβ)) ∎h }) })
    
    abstract
      l→r→l : (a : Σ (M → TyCon) (GradedApplicative mon)) → r→l (l→r a) ≡ a
      l→r→l (F , applic) = Σ-eq refl $ ≡-to-≅ $ graded-applicative-eq pure-eq ap-eq fun-eq
        where
          open LaxMonoidalFunctor renaming ( F to MonFunctor )
          open GradedApplicative applic
          open Monoid mon renaming ( ε to ε' )
          
          abstract
            pure-eq : (λ {α} a → GradedApplicative.pure (proj₂ $ r→l $ l→r (F , applic)) {α} a) ≡ pure
            pure-eq = implicit-fun-ext $ λ (α : Type) → fun-ext $ λ (a : α) → ≅-to-≡ $ hbegin
              GradedApplicative.pure (proj₂ $ r→l $ l→r (F , applic)) a
                ≅⟨ refl ⟩
              fmap (λ _ → a) unit
                ≅⟨ hcong₂ (λ X Y → F X α ∋ Y) (≡-to-≅ (sym (Monoid.left-id mon))) (law-applicative-fmap (λ _ → a) unit) ⟩
              (pure (λ _ → a)) <*> unit
                ≅⟨ hcong₂ (λ X Y → F X α ∋ Y) (≡-to-≅ (Monoid.left-id mon)) (law-homomorphism (lift tt) (λ _ → a)) ⟩
              pure a ∎h
            
          abstract
            ap-eq : (λ {i j} {α β} f a → GradedApplicative._<*>_ (proj₂ $ r→l $ l→r (F , applic)) {i} {j} {α} {β} f a) ≡ _<*>_
            ap-eq = implicit-fun-ext
                  $ λ i → implicit-fun-ext
                  $ λ j → implicit-fun-ext
                  $ λ α → implicit-fun-ext
                  $ λ β → fun-ext
                  $ λ f → fun-ext
                  $ λ a → ≅-to-≡ $ hbegin
              GradedApplicative._<*>_ (proj₂ $ r→l $ l→r (F , applic)) f a 
                ≅⟨ refl ⟩
              fmap (λ {(f , a) → f a}) ((fmap _,_ f) <*> a)
                ≅⟨ hcong₂ (λ X Y → F X β ∋ Y) (≡-to-≅ (sym (Monoid.left-id mon))) (law-applicative-fmap (λ {(f , a) → f a}) (fmap _,_ f <*> a)) ⟩
              pure (λ {(f , a) → f a}) <*> ((fmap _,_ f) <*> a)
                ≅⟨ hcong₂ (λ X Y → F (ε' ∙ (X ∙ j)) β ∋ pure (λ { (f , a) → f a }) <*> (Y <*> a)) (≡-to-≅ (sym left-id)) (law-applicative-fmap _,_ f) ⟩
              pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f <*> a)
                ≅⟨ hsym (law-composition (pure (λ {(f , a) → f a})) (pure _,_ <*> f) a) ⟩
              pure _∘′_ <*> pure (λ {(f , a) → f a}) <*> (pure _,_ <*> f) <*> a
                ≅⟨ hcong₂ (λ X Y → F ((X ∙ (ε' ∙ i)) ∙ j) β ∋ Y <*> (pure _,_ <*> f) <*> a) (≡-to-≅ left-id) (law-homomorphism (λ {(f , a) → f a}) _∘′_) ⟩
              pure (_∘′_ (λ {(f , a) → f a})) <*> (pure _,_ <*> f) <*> a
                ≅⟨ hcong₂ (λ X Y → F (X ∙ j) β ∋ Y <*> a)
                          (≡-to-≅ (trans (cong (λ Z → Z ∙ (ε' ∙ i)) (sym left-id)) (Monoid.assoc mon)))
                          (hsym (law-composition (pure (_∘′_ (λ {(f , a) → f a}))) (pure _,_) f)) ⟩
              pure _∘′_ <*> pure (_∘′_ (λ {(f , a) → f a})) <*> pure _,_ <*> f <*> a
                ≅⟨ hcong₂ (λ X Y → F (((X ∙ ε') ∙ i) ∙ j) β ∋ Y <*> pure _,_ <*> f <*> a) (≡-to-≅ left-id) (law-homomorphism (_∘′_ (λ {(f , a) → f a})) _∘′_) ⟩
              pure (_∘′_ (_∘′_ (λ {(f , a) → f a}))) <*> pure _,_ <*> f <*> a
                ≅⟨ hcong₂ (λ X Y → F ((X ∙ i) ∙ j) β ∋ Y <*> f <*> a) (≡-to-≅ left-id) (law-homomorphism _,_ (_∘′_ (_∘′_ (λ {(f , a) → f a})))) ⟩
              pure ((_∘′_ (λ {(f , a) → f a})) ∘′ _,_) <*> f <*> a
                ≅⟨ refl ⟩
              pure (λ x → x) <*> f <*> a
                ≅⟨ hcong₂ (λ X Y → F (X ∙ j) β ∋ Y <*> a) (≡-to-≅ left-id) (law-id f) ⟩
              f <*> a ∎h
            
          abstract
            fun-eq : GradedApplicative.functor (proj₂ $ r→l $ l→r (F , applic)) ≡ GradedApplicative.functor applic
            fun-eq = fun-ext $ λ (i : M) → Haskell.Functor.functor-eq refl

LaxMonoidalFunctor↔GradedApplicative
  : {ℓ : Level} → {M : Set ℓ} → (mon : Monoid M)
  → LaxMonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {zero}) (setMonoidalCategory {zero}) ↔ (Σ (M → TyCon) (GradedApplicative mon))
LaxMonoidalFunctor↔GradedApplicative {ℓ} {M} mon = bsym $ GradedApplicative↔LaxMonoidalFunctor mon
