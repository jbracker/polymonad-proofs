
open import Level
open import Function hiding ( _∘_ ; id )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst )

open import Bijection renaming ( refl to brefl ; sym to bsym ; trans to btrans )
open import Extensionality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal.Examples.FunctorWithComposition renaming ( functorMonoidalCategory to Fun )
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Monad.Definition
open import Theory.TwoCategory.Examples.Functor using ( Cat )
open import Theory.TwoCategory.Examples.Unit
open import Theory.TwoCategory.Examples.Monoid
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Equality
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.ConstZeroCell.Equality
open import Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor
open import Theory.TwoFunctor.Properties.IsomorphicMonad

module Theory.Functor.Monoidal.Properties.IsomorphicMonad where

LaxMonoidalFunctor↔Monad : {ℓC₀ ℓC₁ : Level}
                         → (C : Category {ℓC₀} {ℓC₁})
                         → (LaxMonoidalFunctor (monoidMonoidalCategory unitMonoid) (Fun C)) 
                         ↔ (Σ (Functor C C) Monad)
LaxMonoidalFunctor↔Monad {ℓC₀} {ℓC₁} C = btrans (LaxMonoidalFunctor↔LaxTwoFunctor unitMonoid C) (btrans (iso Cat C) (ConstLaxTwoFunctor↔Monad C))
  where
    open StrictTwoCategory
    
    iso : {ℓC₀ ℓC₁ ℓC₂ : Level} → (C : StrictTwoCategory {ℓC₀} {ℓC₁} {ℓC₂}) (c : Cell₀ C)
        → (ConstLaxTwoFunctor (monoidTwoCategory unitMonoid) C c) ↔ (ConstLaxTwoFunctor ⊤-TwoCat C c)
    iso C c = bijection l→r r→l (λ b → refl) l→r→l
      where
        l→r : ConstLaxTwoFunctor (monoidTwoCategory unitMonoid) C c → ConstLaxTwoFunctor ⊤-TwoCat C c
        l→r F = const-lax-two-functor (λ {_} {_} → functor (λ _ → [ P₁ ]₀ tt) (λ _ → [ P₁ ]₁ refl) (Functor.id P₁) (Functor.compose P₁))
                                      η μ laxFunId₁ laxFunId₂ laxFunAssoc (λ f → μ-natural₁ f) (λ f → μ-natural₂ f)
                                      where open ConstLaxTwoFunctor F
        
        r→l : ConstLaxTwoFunctor ⊤-TwoCat C c → ConstLaxTwoFunctor (monoidTwoCategory unitMonoid) C c
        r→l F = const-lax-two-functor (λ {_} {_} → functor (λ _ → [ P₁ ]₀ tt) (λ _ → [ P₁ ]₁ tt) (Functor.id P₁) (Functor.compose P₁)) 
                                      η μ  laxFunId₁ laxFunId₂ laxFunAssoc (λ f → μ-natural₁ f) (λ f → μ-natural₂ f) 
                                      where open ConstLaxTwoFunctor F
        
        abstract
          l→r→l : (F : ConstLaxTwoFunctor (monoidTwoCategory unitMonoid) C c) → r→l (l→r F) ≡ F
          l→r→l F = const-lax-two-functor-eq (implicit-fun-ext (λ x → implicit-fun-ext (λ y → functor-eq refl (het-implicit-fun-ext hrefl (λ a → het-implicit-fun-ext hrefl (λ b → het-fun-ext hrefl (eq {a} {b}))))))) 
                                             hrefl hrefl
            where eq : {a b : Category.Obj (HomCat (monoidTwoCategory unitMonoid) tt tt)} 
                     → (f : Category.Hom (HomCat (monoidTwoCategory unitMonoid) tt tt) tt tt) 
                     → Functor.F₁ (ConstLaxTwoFunctor.P₁ (r→l (l→r F))) {a} {b} f ≅ Functor.F₁ (ConstLaxTwoFunctor.P₁ F) {a} {b} f
                  eq {tt} {tt} refl = hrefl
