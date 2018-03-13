
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ ) 
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ )

open import Equality
open import Extensionality
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid renaming ( monoidCategory' to MonCat' )
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Equality
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Equality

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.ToGradedLaxMonoidalFunctor where

IndexedLaxMonoidalFunctor→GradedLaxMonoidalFunctor : {ℓMon ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                                                   → {M : Set ℓMon}
                                                   → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                                   → (Mon : Monoid M)
                                                   → (CM : MonoidalCategory C) (DM : MonoidalCategory D)
                                                   → (IndexedLaxMonoidalFunctor (MonCat' Mon) CM DM)
                                                   → (GradedLaxMonoidalFunctor Mon CM DM)
IndexedLaxMonoidalFunctor→GradedLaxMonoidalFunctor Mon CM DM IxLMF = 
  gradedLaxMonoidalFunctor F (ε tt) μ-nat assoc left-unitality right-unitality
  where
    open IndexedLaxMonoidalFunctor IxLMF renaming ( μ-natural-transformation to μ-nat )
