
open import Level
open import Function

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( ≅-to-≡ ; ≡-to-≅ )
open ≡-Reasoning

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym )
open import Theory.Category.Definition
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Natural.Transformation
open import Theory.Monad.Definition hiding ( monad )
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.Unit
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.ConstZeroCell.Equality
open import Theory.TwoFunctor.Equality
open import Theory.TwoFunctor.Properties.ToMonad
open import Theory.TwoFunctor.Properties.FromMonad
 
module Theory.TwoFunctor.Properties.IsomorphicMonad where


Monad↔LaxTwoFunctor : {ℓC₀ ℓC₁ : Level} → Σ (Category {ℓC₀} {ℓC₁}) (λ C → Σ (Functor C C) Monad) ↔ LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁})
Monad↔LaxTwoFunctor {ℓC₀} {ℓC₁} = bijection l→r r→l r→l→r l→r→l
  where
    Category' = Category {ℓC₀} {ℓC₁}
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    l→r : Σ Category' (λ C → Σ (Functor C C) Monad) → LaxTwoFunctor ⊤-TwoCat Cat'
    l→r (C , F , monad) = Monad→LaxTwoFunctor {C = C} {M = F} monad
    
    r→l : LaxTwoFunctor ⊤-TwoCat Cat' → Σ Category' (λ C → Σ (Functor C C) Monad)
    r→l F = LaxTwoFunctor.P₀ F tt , Functor.F₀ (LaxTwoFunctor.P₁ F) tt , LaxTwoFunctor→Monad F
    
    abstract
      r→l→r : (F : LaxTwoFunctor ⊤-TwoCat Cat) → l→r (r→l F) ≡ F
      r→l→r F = lax-two-functor-eq refl (≡-to-≅ P₁-eq) (≡-to-≅ (implicit-fun-ext (λ x → refl))) (≡-to-≅ (implicit-fun-ext (λ x → refl)))
        where
          p : (c : Category.Obj (LaxTwoFunctor.P₀ (l→r (r→l F)) tt)) 
            → Category.id (proj₁ (r→l F)) ≡ NaturalTransformation.η (Functor.F₁ (LaxTwoFunctor.P₁ F) tt) c
          p c = begin
            Category.id (proj₁ (r→l F))
              ≡⟨ refl ⟩
            NaturalTransformation.η (Id⟨ Functor.F₀ (LaxTwoFunctor.P₁ F) tt ⟩) c
              ≡⟨ cong (λ X → NaturalTransformation.η X c) (sym (Functor.id (LaxTwoFunctor.P₁ F))) ⟩
            NaturalTransformation.η (Functor.F₁ (LaxTwoFunctor.P₁ F) tt) c ∎
          
          P₁-eq : (λ {x y} → LaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y}) ≡ LaxTwoFunctor.P₁ F
          P₁-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → functor-eq refl $ ≡-to-≅ $ implicit-fun-ext 
                $ λ f → implicit-fun-ext $ λ g → fun-ext 
                $ λ F → natural-transformation-eq $ fun-ext $ p
    
    abstract
      l→r→l : (M : Σ Category (λ C → Σ (Functor C C) Monad)) → r→l (l→r M) ≡ M
      l→r→l (C , F , monad) = Σ-eq refl (het-Σ-eq refl (≡-to-≅ (monad-eq refl refl)))




LaxTwoFunctor↔Monad : {ℓC₀ ℓC₁ : Level} → LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁}) ↔ Σ (Category {ℓC₀} {ℓC₁}) (λ C → Σ (Functor C C) Monad)
LaxTwoFunctor↔Monad {ℓC₀} {ℓC₁} = Bijection.sym $ Monad↔LaxTwoFunctor {ℓC₀} {ℓC₁}

Monad↔ConstLaxTwoFunctor : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
                         → (Σ (Functor C C) Monad)
                         ↔ (ConstLaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁}) C)
Monad↔ConstLaxTwoFunctor {ℓC₀} {ℓC₁} C = bijection l→r r→l r→l→r l→r→l
  where
    Category' = Category {ℓC₀} {ℓC₁}
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    l→r : Σ (Functor C C) Monad → ConstLaxTwoFunctor ⊤-TwoCat Cat' C
    l→r (F , monad) = Monad→ConstLaxTwoFunctor {C = C} {M = F} monad
    
    r→l : ConstLaxTwoFunctor ⊤-TwoCat Cat' C → Σ (Functor C C) Monad
    r→l F = Functor.F₀ (ConstLaxTwoFunctor.P₁ F) tt , ConstLaxTwoFunctor→Monad F
    
    abstract
      r→l→r : (F : ConstLaxTwoFunctor ⊤-TwoCat Cat C) → l→r (r→l F) ≡ F
      r→l→r F = const-lax-two-functor-eq P₁-eq (≡-to-≅ (implicit-fun-ext (λ x → refl))) (≡-to-≅ (implicit-fun-ext (λ x → refl)))
        where
          p : (c : Category.Obj (ConstLaxTwoFunctor.P₀ (l→r (r→l F)) tt)) 
            → Category.id C ≡ NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) tt) c
          p c = begin
            Category.id C
              ≡⟨ refl ⟩
            NaturalTransformation.η (Id⟨ Functor.F₀ (ConstLaxTwoFunctor.P₁ F) tt ⟩) c
              ≡⟨ cong (λ X → NaturalTransformation.η X c) (sym (Functor.id (ConstLaxTwoFunctor.P₁ F))) ⟩
            NaturalTransformation.η (Functor.F₁ (ConstLaxTwoFunctor.P₁ F) tt) c ∎
          
          P₁-eq : (λ {x y} → ConstLaxTwoFunctor.P₁ (l→r (r→l F)) {x} {y}) ≡ ConstLaxTwoFunctor.P₁ F
          P₁-eq = implicit-fun-ext $ λ x → implicit-fun-ext $ λ y → functor-eq refl $ ≡-to-≅ $ implicit-fun-ext 
                $ λ f → implicit-fun-ext $ λ g → fun-ext 
                $ λ F → natural-transformation-eq $ fun-ext $ p
    
    abstract
      l→r→l : (M : Σ (Functor C C) Monad) → r→l (l→r M) ≡ M
      l→r→l (F , monad) = Σ-eq refl (≡-to-≅ (monad-eq refl refl))

ConstLaxTwoFunctor↔Monad : {ℓC₀ ℓC₁ : Level} (C : Category {ℓC₀} {ℓC₁}) 
                         → (ConstLaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁}) C) ↔ (Σ (Functor C C) Monad)
ConstLaxTwoFunctor↔Monad C = Bijection.sym $ Monad↔ConstLaxTwoFunctor C
