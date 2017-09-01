
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

-- Local
open import Extensionality
open import Bijection renaming ( refl to brefl )
open import Utilities
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid
open import Theory.Category.Examples.Discrete
open import Theory.Category.Examples.Functor
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Category.Monoidal.Examples.FunctorWithComposition renaming ( functorMonoidalCategory to Fun )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.Natural.Transformation.Examples.FunctorCompositionAssociator
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor renaming ( Cat to Cat' )
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.TwoFunctor.ConstZeroCell.Equality
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.Properties.FromLaxMonoidalFunctor
open import Theory.TwoFunctor.Properties.ToLaxMonoidalFunctor

open Category hiding ( left-id ; right-id ; assoc )
open StrictTwoCategory hiding ( left-id ; right-id ; assoc )
 
module Theory.TwoFunctor.Properties.IsomorphicLaxMonoidalFunctor where

LaxMonoidalFunctor↔LaxTwoFunctor : {ℓE ℓC₀ ℓC₁ : Level}
                                 → {Eff : Set ℓE}
                                 → (mon : Monoid Eff)
                                 → (C : Category {ℓC₀} {ℓC₁})
                                 → (LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun C))
                                 ↔ (ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory mon)) Cat' C)
LaxMonoidalFunctor↔LaxTwoFunctor {ℓE} {ℓC₀} {ℓC₁} {Eff} mon C 
  = bijection (LaxMonoidalFunctor→LaxTwoFunctor mon C) (LaxTwoFunctor→LaxMonoidalFunctor mon C) id' id''
  where
    Mon = monoidMonoidalCategory mon
    Mon₂ = discreteHomCatTwoCategory (monoidCategory mon)
    
    id' : (b : ConstLaxTwoFunctor Mon₂ Cat' C) 
        → LaxMonoidalFunctor→LaxTwoFunctor mon C (LaxTwoFunctor→LaxMonoidalFunctor mon C b) ≡ b
    id' b = const-lax-two-functor-eq 
            (implicit-fun-ext (λ x → implicit-fun-ext (λ y → functor-eq refl hrefl))) 
            (het-implicit-fun-ext hrefl (λ i → hrefl)) 
            (het-implicit-fun-ext hrefl (λ x → het-implicit-fun-ext hrefl (λ y → het-implicit-fun-ext hrefl (λ z → het-implicit-fun-ext hrefl (λ f → het-implicit-fun-ext hrefl (λ g → hrefl))))))
    
    id'' : (a : LaxMonoidalFunctor (monoidMonoidalCategory mon) (Fun C)) 
         → LaxTwoFunctor→LaxMonoidalFunctor mon C (LaxMonoidalFunctor→LaxTwoFunctor mon C a) ≡ a
    id'' a = lax-monoidal-functor-eq refl hrefl (het-natural-transformation-eq refl refl hrefl)
