
open import Level

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl )

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition

 
module Theory.Functor.Examples.ProductSwap where


productSwapFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                   → (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁})
                   → Functor (C ×C D) (D ×C C)
productSwapFunctor C D = functor swap₀ swap₁ refl refl
  where
    open Category
    
    swap₀ : Obj (C ×C D) → Obj (D ×C C)
    swap₀ (c , d) = (d , c)
    
    swap₁ : {a b : Obj (C ×C D)} → Hom (C ×C D) a b → Hom (D ×C C) (swap₀ a) (swap₀ b)
    swap₁ (f , g) = (g , f)

SwapFun = productSwapFunctor

abstract
  product-swap-functor-self-inverse : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level}
                                    → (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁})
                                    → [ SwapFun C D ]∘[ SwapFun D C ] ≡ Id[ D ×C C ]
  product-swap-functor-self-inverse C D = functor-eq refl hrefl

