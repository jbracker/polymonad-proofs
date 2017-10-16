
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ ) 
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ )

open import Equality
open import Extensionality
open import Bijection renaming ( sym to bsym )
open import Theory.Category.Definition renaming ( unitCategory to UnitCat )
open import Theory.Category.Monoidal
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Equality

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.ToLaxMonoidalFunctor where 

IndexedLaxMonoidalFunctor→LaxMonoidalFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                                             → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                             → (CM : MonoidalCategory C) (DM : MonoidalCategory D)
                                             → (IndexedLaxMonoidalFunctor UnitCat CM DM)
                                             → (LaxMonoidalFunctor CM DM)
IndexedLaxMonoidalFunctor→LaxMonoidalFunctor CM DM IxLMF = 
  laxMonoidalFunctor (F tt) (ε tt) (μ-nat tt tt) 
                     (λ x y z → ≅-to-≡ $ assoc x y z) 
                     (λ x → ≅-to-≡ $ left-unitality x) 
                     (λ x → ≅-to-≡ $ right-unitality x)
  where
    open IndexedLaxMonoidalFunctor IxLMF renaming ( μ-natural-transformation to μ-nat )
