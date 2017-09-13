
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

module Theory.TwoFunctor.Properties.ToIndexedMonad where

LaxTwoFunctor→IndexedMonad
  : {ℓIxs ℓC₀ ℓC₁ : Level}
  → {C : Category {ℓC₀} {ℓC₁}}
  → {Ixs : Set ℓIxs}
  → (F : ConstLaxTwoFunctor (discreteHomCatTwoCategory (codiscreteCategory Ixs)) (Cat {ℓC₀} {ℓC₁}) C)
  → IndexedMonad Ixs (λ i j → [ ConstLaxTwoFunctor.P₁ F {i} {j} ]₀ (lift tt))
LaxTwoFunctor→IndexedMonad {ℓIxs} {ℓC₀} {ℓC₁} {C} {Ixs} F = indexed-monad (ConstLaxTwoFunctor.η F) (ConstLaxTwoFunctor.μ F) assoc' left-id' right-id'
  where
    open ConstLaxTwoFunctor F
    open NaturalTransformation renaming (η to nat-η)
    
    Ixs₁ = codiscreteCategory Ixs
    Ixs₂ = discreteHomCatTwoCategory Ixs₁
    Cat' = Cat {ℓC₀} {ℓC₁}
    
    _∘C_ = Category._∘_ C
    
    M : Ixs → Ixs → Functor C C
    M i j = [ P₁ {i} {j} ]₀ (lift tt)
    
    abstract
      nat-eq : {F G H I : Functor C C} → {α : NaturalTransformation F G} {β : NaturalTransformation H I}
             → F ≡ H → G ≡ I → α ≅ β → (x : Obj C) 
             → nat-η α x ≅ nat-η β x
      nat-eq refl refl hrefl x = hrefl
    
    abstract
      assoc' : {i j k l : Ixs} {x : Obj C}
             → nat-η (μ {i} {j} {l}) x ∘C [ M j l ]₁ (nat-η (μ {i} {k} {j}) x) 
             ≡ nat-η (μ {i} {k} {l}) x ∘C nat-η (μ {k} {j} {l}) ([ M i k ]₀ x)
      assoc' {i} {j} {k} {l} {x} = begin
        nat-η (μ {i} {j} {l}) x ∘C [ M j l ]₁ (nat-η (μ {i} {k} {j}) x) 
          ≡⟨ cong (λ X → nat-η (μ {i} {j} {l}) x ∘C X) (sym (Category.right-id C)) ⟩
        nat-η (μ {i} {j} {l}) x ∘C (id C {[ [ M j l ]∘[ M i j ] ]₀ x} ∘C [ M j l ]₁ (nat-η (μ {i} {k} {j}) x))
          ≡⟨⟩
        nat-η ((Cat ∘ᵥ μ) ((Cat ∘ₕ id₂ Cat) μ)) x
          ≡⟨ ≅-to-≡ (nat-eq (functor-eq refl hrefl) (functor-eq refl hrefl) (laxFunAssoc {i} {k} {j} {l}) x) ⟩
        nat-η ((Cat ∘ᵥ μ) ((Cat ∘ₕ μ) (id₂ Cat))) x
          ≡⟨⟩
        nat-η (μ {i} {k} {l}) x ∘C (nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∘C [ [ M j l ]∘[ M k j ] ]₁ (id C {[ M i k ]₀ x}))
          ≡⟨ cong (λ X → nat-η (μ {i} {k} {l}) x ∘C (nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∘C [ M j l ]₁ X)) (Functor.id (M k j)) ⟩
        nat-η (μ {i} {k} {l}) x ∘C (nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∘C [ M j l ]₁ (id C {[ [ M k j ]∘[ M i k ] ]₀ x}))
          ≡⟨ cong (λ X → nat-η (μ {i} {k} {l}) x ∘C (nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∘C X)) (Functor.id (M j l)) ⟩
        nat-η (μ {i} {k} {l}) x ∘C (nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∘C id C {[ [ M j l ]∘[ [ M k j ]∘[ M i k ] ] ]₀ x})
          ≡⟨ cong (λ X → nat-η (μ {i} {k} {l}) x ∘C X) (Category.left-id C) ⟩
        nat-η (μ {i} {k} {l}) x ∘C nat-η (μ {k} {j} {l}) ([ M i k ]₀ x) ∎
   
    abstract
      left-id' : {i j : Ixs} {x : Obj C}
               → nat-η (μ {i} {i} {j}) x ∘C [ M i j ]₁ (nat-η (η {i}) x) ≡ nat-η Id⟨ M i j ⟩ x
      left-id' {i} {j} {x} = begin
        nat-η (μ {i} {i} {j}) x ∘C [ M i j ]₁ (nat-η (η {i}) x) 
          ≡⟨ cong (λ X → nat-η (μ {i} {i} {j}) x ∘C X) (sym $ Category.right-id C) ⟩
        nat-η (μ {i} {i} {j}) x ∘C (id C {[ [ M i j ]∘[ M i i ] ]₀ x} ∘C [ M i j ]₁ (nat-η (η {i}) x))
          ≡⟨ ≅-to-≡ (nat-eq (functor-eq refl hrefl) (functor-eq refl hrefl) laxFunId₁ x) ⟩
        nat-η Id⟨ M i j ⟩ x ∎
    
    abstract
      right-id' : {i j : Ixs} {x : Obj C}
                → nat-η (μ {i} {j} {j}) x ∘C (nat-η (η {j}) ([ M i j ]₀ x)) ≡ nat-η Id⟨ M i j ⟩ x
      right-id' {i} {j} {x} = begin
        nat-η (μ {i} {j} {j}) x ∘C nat-η (η {j}) ([ M i j ]₀ x) 
          ≡⟨ cong (λ X → nat-η (μ {i} {j} {j}) x ∘C X) (sym (Category.left-id C)) ⟩
        nat-η (μ {i} {j} {j}) x ∘C (nat-η (η {j}) ([ M i j ]₀ x) ∘C id C {[ M i j ]₀ x}) 
          ≡⟨ ≅-to-≡ (nat-eq (functor-eq refl hrefl) (functor-eq refl hrefl) laxFunId₂ x) ⟩
        nat-η Id⟨ M i j ⟩ x ∎
