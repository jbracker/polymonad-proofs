
-- Stdlib
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

-- Local
open import Extensionality
open import Utilities
open import Theory.Triple
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Monoid
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Natural.Transformation.Examples
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoCategory.Examples.Monoid
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.Haskell.Parameterized.Graded.Monad

open Category hiding ( left-id ; right-id ; assoc ) renaming (id to idC)
open StrictTwoCategory hiding ( left-id ; right-id ; assoc )

module Theory.TwoFunctor.Properties.ToGradedMonad where

LaxTwoFunctor→GradedMonad
  : {ℓMon ℓC₀ ℓC₁ : Level}
  → {C : Category {ℓC₀} {ℓC₁}}
  → {Mon : Set ℓMon}
  → {monoid : Monoid Mon}
  → (F : ConstLaxTwoFunctor (monoidTwoCategory monoid) (Cat {ℓC₀} {ℓC₁}) C)
  → GradedMonad monoid (λ i → [ ConstLaxTwoFunctor.P₁ F {tt} {tt} ]₀ i)
LaxTwoFunctor→GradedMonad {ℓMon} {ℓC₀} {ℓC₁} {C} {Mon} {monoid} F 
  = graded-monad η μ μ-coher η-left-coher η-right-coher
  where
    open ConstLaxTwoFunctor F
    open Monoid monoid
    open NaturalTransformation renaming (η to nat-η)
    
    M = λ i → [ P₁ {tt} {tt} ]₀ i
    Cat' = Cat {ℓC₀} {ℓC₁}

    _∘C_ = Category._∘_ C
    
    MonCat₁ = monoidCategory monoid
    MonCat₂ = monoidTwoCategory monoid
    
    abstract
      nat-eq : {F G F' G' : Functor C C} {α : NaturalTransformation F G} {β : NaturalTransformation F' G'} {c : Obj C}
             → F ≡ F' → G ≡ G' → α ≅ β → (Hom C ([ F ]₀ c) ([ G ]₀ c) ∋ nat-η α c) ≅ (Hom C ([ F' ]₀ c) ([ G' ]₀ c) ∋ nat-η β c)
      nat-eq refl refl hrefl = hrefl

    abstract
      μ-coher : {i j k : Mon} {c : Obj C} 
              → nat-η (μ {f = j ∙ k} {i}) c ∘C ([ M i ]₁ (nat-η (μ {f = k} {j}) c)) 
              ≅ nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c))
      μ-coher {i} {j} {k} {c} = hbegin
        nat-η (μ {f = j ∙ k} {i}) c ∘C ([ M i ]₁ (nat-η (μ {f = k} {j}) c)) 
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {f = j ∙ k} {i}) c ∘C X) (sym (Category.right-id C)) ⟩
        nat-η (μ {f = j ∙ k} {i}) c ∘C (idC C {[ M i ]₀ ([ M (j ∙ k) ]₀ c)} ∘C [ M i ]₁ (nat-η (μ {f = k} {j}) c)) 
          ≅⟨ hrefl ⟩
        nat-η (μ {f = j ∙ k} {i}) c ∘C nat-η ( ⟨ Id⟨ M i ⟩ ⟩∘ₕ⟨ μ {f = k} {j} ⟩ ) c 
          ≅⟨ hrefl ⟩
        (Hom C ([ [ M i ]∘[ [ M j ]∘[ M k ] ] ]₀ c) ([ M (i ∙ (j ∙ k)) ]₀ c) ∋ nat-η ⟨ μ {f = j ∙ k} {i} ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = M i} ⟩∘ₕ⟨ μ {f = k} {j} ⟩ ⟩ c)
          ≅⟨ nat-eq (functor-eq refl hrefl) (cong (λ X → M X) assoc) (laxFunAssoc {f = k} {j} {i}) ⟩
        (Hom C ([ [ [ M i ]∘[ M j ] ]∘[ M k ] ]₀ c) ([ M ((i ∙ j) ∙ k) ]₀ c) ∋ nat-η ⟨ μ {f = k} {i ∙ j} ⟩∘ᵥ⟨ ⟨ μ {f = j} {i} ⟩∘ₕ⟨ id₂ Cat' {f = M k} ⟩ ⟩ c)
          ≅⟨ hrefl ⟩
        nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c) ∘C [ [ M i ]∘[ M j ] ]₁ (idC C {[ M k ]₀ c}) )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c) ∘C [ M i ]₁ X)) (Functor.id (M j)) ⟩
        nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c) ∘C [ M i ]₁ (idC C {[ M j ]₀ ([ M k ]₀ c)}) )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c) ∘C X)) (Functor.id (M i)) ⟩
        nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c) ∘C idC C {[ M i ]₀ ([ M j ]₀ ([ M k ]₀ c))} )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {f = k} {i ∙ j}) c ∘C X) (Category.left-id C) ⟩
        nat-η (μ {f = k} {i ∙ j}) c ∘C (nat-η (μ {f = j} {i}) ([ M k ]₀ c)) ∎h
    
    abstract
      η-left-coher : {i : Mon} {c : Obj C} 
                   → nat-η μ c ∘C ([ M i ]₁ (nat-η η c)) 
                   ≅ nat-η Id⟨ M i ⟩ c
      η-left-coher {i} {c} = hbegin
        nat-η μ c ∘C ([ M i ]₁ (nat-η η c)) 
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μ c ∘C X) (sym $ Category.right-id C) ⟩
        nat-η μ c ∘C (idC C {[ [ M i ]∘[ M ε ] ]₀ c} ∘C [ M i ]₁ (nat-η η c)) 
          ≅⟨ nat-eq (StrictTwoCategory.left-id Cat') (cong M right-id) laxFunId₁ ⟩
        nat-η Id⟨ M i ⟩ c ∎h
    
    p : {i : Mon} 
      → (NaturalTransformation [ Id[ C ] ]∘[ M i ] (M (ε ∙ i)) ∋ ⟨ μ {f = i} {ε} ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ id₂ Cat' {f = M i} ⟩ ⟩) 
      ≅ (NaturalTransformation (M i) (M i) ∋ Id⟨ M i ⟩)
    p = laxFunId₂
    
    abstract
      η-right-coher : {i : Mon} {c : Obj C} 
                    → nat-η μ c ∘C (nat-η η ([ M i ]₀ c)) 
                    ≅ nat-η Id⟨ M i ⟩ c
      η-right-coher {i} {c} = hbegin
        nat-η μ c ∘C (nat-η η ([ M i ]₀ c)) 
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μ c ∘C X) (sym (Category.left-id C)) ⟩
        nat-η μ c ∘C (nat-η η ([ M i ]₀ c) ∘C idC C {[ M i ]₀ c}) 
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μ c ∘C (nat-η η ([ M i ]₀ c) ∘C X)) (sym (Functor.id (M i))) ⟩
        (Hom C ([ [ Id[ C ] ]∘[ M i ] ]₀ c) ([ M (ε ∙ i) ]₀ c) ∋ nat-η (μ {f = i} {ε}) c ∘C (nat-η η ([ M i ]₀ c) ∘C [ M i ]₁ (idC C {c})))
          ≅⟨ hrefl ⟩
        (Hom C ([ [ Id[ C ] ]∘[ M i ] ]₀ c) ([ M (ε ∙ i) ]₀ c) ∋ nat-η (μ {f = i} {ε}) c ∘C (nat-η ⟨ η ⟩∘ₕ⟨ id₂ Cat' {f = {!M ?!}} ⟩ c))
        -- (Hom C ([ [ Id[ C ] ]∘[ M i ] ]₀ c) ([ M (ε ∙ i) ]₀ c) ∋ nat-η ( ⟨ μ {f = i} {ε} ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ id₂ Cat' {f = M i} ⟩ ⟩ ) c)
          ≅⟨ {!!} ⟩
        (Hom C ([ M i ]₀ c) ([ M i ]₀ c) ∋ nat-η Id⟨ M i ⟩ c) ∎h
{-


    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → μ {x} {y} {y} {f} {id₁ C {y}} ∘Dᵥ (η {y} ∘Dₕ id₂ D {f = [ P₁ {x} {y} ]₀ f}) 
              ≅ id₂ D {f = [ P₁ {x} {y} ]₀ f}

-}
