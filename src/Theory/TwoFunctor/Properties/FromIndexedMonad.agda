
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ ; proof-irrelevance to hproof-irrelevance )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Utilities
open import Haskell
open import Haskell.Functor hiding ( functor ; functor-eq ) renaming ( Functor to HaskellFunctor )
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.ConstZeroCell

open Category
open StrictTwoCategory

module Theory.TwoFunctor.Properties.FromIndexedMonad where

IndexedMonad→LaxTwoFunctor
  : {ℓIxs ℓC₀ ℓC₁ : Level}
  → {C : Category {ℓC₀} {ℓC₁}}
  → {Ixs : Set ℓIxs}
  → {M : Ixs → Ixs → Functor C C}
  → (monad : IndexedMonad Ixs M)
  → ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {ℓC₀} {ℓC₁}) C
IndexedMonad→LaxTwoFunctor {ℓIxs} {ℓC₀} {ℓC₁} {C} {Ixs} {M} monad = record
  { P₁ = λ {i} {j} → P {i} {j}
  ; η = λ {i} → η {i}
  ; μ = λ {i} {j} {k} {_} {_} → μ {i} {j} {k}
  ; laxFunId₁ = λ {i} {j} {_} → lawFunId₁ {i} {j}
  ; laxFunId₂ = λ {i} {j} {_} → lawFunId₂ {i} {j}
  ; laxFunAssoc = λ {i} {j} {k} {l} {_} {_} {_} → lawFunAssoc {i} {j} {k} {l}
  ; μ-natural₁ = λ { {i} {j} {k} (lift tt) {lift tt} {lift tt} {refl} → μ-natural {i} {j} {k}}
  ; μ-natural₂ = λ { {i} {j} {k} (lift tt) {lift tt} {lift tt} {refl} → μ-natural {i} {j} {k}}
  }
  where
    Ixs₁ = codiscreteCategory Ixs
    Ixs₂ = discreteHomCatTwoCategory Ixs₁
    Cat' = Cat {ℓC₀} {ℓC₁}

    _∘Ixs_ = Category._∘_ Ixs₁
    _∘C_ = Category._∘_ C

    open IndexedMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    P : {i j : Ixs} → Functor (HomCat Ixs₂ i j) (HomCat Cat' C C)
    P {i} {j} = Functor.functor P₀ P₁ refl (λ {a b c} {f} {g} → P-compose {a} {b} {c} {f} {g})
      where
        P₀ : Obj (HomCat Ixs₂ i j) → Obj (HomCat Cat' C C)
        P₀ (lift tt) = M i j
        
        P₁ : {a b : Obj (HomCat Ixs₂ i j)} → Hom (HomCat Ixs₂ i j) a b → Hom (HomCat Cat' C C) (P₀ a) (P₀ b)
        P₁ {lift tt} {lift tt} refl = Id⟨ P₀ (lift tt) ⟩
        
        abstract
          P-compose : {a b c : Obj (HomCat Ixs₂ i j)} {f : Hom (HomCat Ixs₂ i j) a b} {g : Hom (HomCat Ixs₂ i j) b c}
                    → P₁ (Category._∘_ (HomCat Ixs₂ i j) g f) ≡ ⟨ P₁ g ⟩∘ᵥ⟨ P₁ f ⟩
          P-compose {lift tt} {lift tt} {lift tt} {refl} {refl} = sym (left-id (HomCat Cat' C C))

    abstract
      μ-natural : {i j k : Ixs}
                → ⟨ Id⟨ M i k ⟩ ⟩∘ᵥ⟨ μ ⟩
                ≡ ⟨ μ ⟩∘ᵥ⟨ ⟨ Id⟨ M j k ⟩ ⟩∘ₕ⟨ Id⟨ M i j ⟩ ⟩ ⟩
      μ-natural {i} {j} {k} = trans (StrictTwoCategory.vertical-right-id Cat) 
                            $ trans (sym (StrictTwoCategory.vertical-left-id Cat)) 
                            $ cong (λ X → ⟨ μ ⟩∘ᵥ⟨ X ⟩) (sym (id∘ₕid≡id Cat))
    
    abstract
      lawFunId₁ : {i j : Ixs}
                → ⟨ μ {i} {i} {j} ⟩∘ᵥ⟨ ⟨ Id⟨ M i j ⟩ ⟩∘ₕ⟨ η {i} ⟩ ⟩ ≅ id₂ Cat {C}
      lawFunId₁ {i} {j} = het-natural-transformation-eq (StrictTwoCategory.left-id Cat) refl $ het-fun-ext hrefl 
                        $ λ x → ≡-to-≅ $ trans (cong (λ X → nat-η (μ {i} {i} {j}) x ∘C X) (Category.right-id C)) η-left-coher
    
    abstract
      lawFunId₂ : {i j : Ixs}
                  → ⟨ μ {i} {j} {j} ⟩∘ᵥ⟨ ⟨ η {j} ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩ ⟩ ≅ id₂ Cat' {C}
      lawFunId₂ {i} {j} = het-natural-transformation-eq (StrictTwoCategory.right-id Cat) refl $ het-fun-ext hrefl 
                        $ λ x → ≡-to-≅ $ trans (cong (λ X → nat-η (μ {i} {j} {j}) x ∘C X) (Category.left-id C)) η-right-coher
    
    abstract
      lawFunAssoc : {i j k l : Ixs}
                  → ⟨ μ {i} {k} {l} ⟩∘ᵥ⟨ ⟨ Id⟨ M k l ⟩ ⟩∘ₕ⟨ μ {i} {j} {k} ⟩ ⟩
                  ≅ ⟨ μ {i} {j} {l} ⟩∘ᵥ⟨ ⟨ μ {j} {k} {l} ⟩∘ₕ⟨ Id⟨ M i j ⟩ ⟩ ⟩
      lawFunAssoc {i} {j} {k} {l} = het-natural-transformation-eq (StrictTwoCategory.assoc Cat) refl  $ het-fun-ext hrefl 
                                  $ λ x → ≡-to-≅ 
                                  $ trans (cong (λ X → nat-η (μ {i} {k} {l}) x ∘C X) (Category.right-id C)) 
                                  $ trans μ-coher 
                                  $ cong (λ X → nat-η μ x ∘C X) $ sym 
                                  $ trans (cong (λ X → nat-η μ ([ M i j ]₀ x) ∘C X) (Functor.id ([ M k l ]∘[ M j k ]))) (Category.left-id C)
