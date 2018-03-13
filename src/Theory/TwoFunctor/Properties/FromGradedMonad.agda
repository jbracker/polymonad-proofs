
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

open import Extensionality


open import Theory.Triple
open import Theory.Monoid
open import Theory.Category.Definition hiding ( category )
open import Theory.Category.Examples.Monoid
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoCategory.Examples.Monoid
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell
open import Theory.Haskell.Parameterized.Graded.Monad
 
module Theory.TwoFunctor.Properties.FromGradedMonad where

open Category hiding ( right-id ; left-id ; assoc ) renaming ( id to idC )
open StrictTwoCategory hiding ( right-id ; left-id ; assoc )
open Triple

GradedMonad→LaxTwoFunctor
  : {ℓMon ℓC₀ ℓC₁ : Level}
  → {C : Category {ℓC₀} {ℓC₁}}
  → {Mon : Set ℓMon}
  → {monoid : Monoid Mon}
  → {M : Mon → Functor C C}
  → GradedMonad monoid M
  → ConstLaxTwoFunctor (monoidTwoCategory monoid) (Cat {ℓC₀} {ℓC₁}) C
GradedMonad→LaxTwoFunctor {ℓMon} {ℓC₀} {ℓC₁} {C} {Mon} {monoid} {M} monad = record
  { P₁ = λ {i} {j} → P
  ; η = λ {i} → η
  ; μ = λ {i} {j} {k} {f} {g} → μ {g} {f}
  ; laxFunId₁ = λ {x} {y} {i} → lawFunId₁ {x} {y} {i}
  ; laxFunId₂ = λ {x} {y} {i} → lawFunId₂ {x} {y} {i}
  ; laxFunAssoc = λ {w} {x} {y} {z} {i} {j} {k} → lawFunAssoc {w} {x} {y} {z} {i} {j} {k}
  ; μ-natural₁ = λ { {a} {b} {c} f {x} {.x} {refl} → μ-natural f x }
  ; μ-natural₂ = λ { {a} {b} {c} g {x} {.x} {refl} → μ-natural x g }
  }
  where
    monCat₁ = monoidCategory monoid
    monCat₂ = monoidTwoCategory monoid
    Cat' = Cat {ℓC₀} {ℓC₁}

    _∘C_ = Category._∘_ C
    _∘Eff_ = Category._∘_ monCat₁
    
    open Monoid monoid
    open GradedMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    F = M
    
    P : Functor (HomCat monCat₂ tt tt) (HomCat Cat' C C)
    P = Functor.functor P₀ P₁ refl compose
      where
        P₀ : Obj (HomCat monCat₂ tt tt) → Obj (HomCat Cat' C C)
        P₀ i = F i
       
        P₁ : {a b : Obj (HomCat monCat₂ tt tt)} → Hom (HomCat monCat₂ tt tt) a b → Hom (HomCat Cat' C C) (P₀ a) (P₀ b)
        P₁ {i} {.i} refl = Id⟨ P₀ i ⟩
        
        abstract
          compose : {a b c : Obj (HomCat monCat₂ tt tt)}
                  → {f : Hom (HomCat monCat₂ tt tt) a b} {g : Hom (HomCat monCat₂ tt tt) b c}
                  → P₁ (Category._∘_ (HomCat monCat₂ tt tt) g f) ≡ ⟨ P₁ g ⟩∘ᵥ⟨ P₁ f ⟩
          compose {a} {.a} {.a} {refl} {refl} = sym (Category.left-id (HomCat Cat' C C))
    
    abstract
      nat-eq : {F G : Functor C C} {α β : NaturalTransformation F G} → (α ≡ β) → {c : Obj C} → nat-η α c ≡ nat-η β c
      nat-eq refl = refl
    
    abstract
      μ-natural : (f x : Cell₁ monCat₂ tt tt)
                → ⟨ [ P ]₁ refl ⟩∘ᵥ⟨ μ {x} {f} ⟩
                ≡ ⟨ μ {x} {f} ⟩∘ᵥ⟨ ⟨ [ P ]₁ refl ⟩∘ₕ⟨ [ P ]₁ refl ⟩ ⟩
      μ-natural f x 
        = natural-transformation-eq $ fun-ext $ λ (c : Obj C) → begin 
          nat-η ⟨ Id⟨ F (x ∙ f) ⟩ ⟩∘ᵥ⟨ μ {x} {f} ⟩ c
            ≡⟨ nat-eq {α = ⟨ Id⟨ F (x ∙ f) ⟩ ⟩∘ᵥ⟨ μ {x} {f} ⟩} {β = μ {x} {f}} (vertical-right-id Cat') {c = c} ⟩
          nat-η (μ {x} {f}) c
            ≡⟨ nat-eq {α = μ {x} {f}} {β = ⟨ μ {x} {f} ⟩∘ᵥ⟨ Id⟨ [ F x ]∘[ F f ] ⟩ ⟩} (sym $ vertical-left-id Cat') ⟩
          nat-η ⟨ μ {x} {f} ⟩∘ᵥ⟨ Id⟨ [ F x ]∘[ F f ] ⟩ ⟩ c
            ≡⟨ cong (λ X → nat-η ⟨ μ {x} {f} ⟩∘ᵥ⟨ X ⟩ c) (sym $ id∘ₕid≡id Cat') ⟩
          nat-η ⟨ μ {x} {f} ⟩∘ᵥ⟨ ⟨ Id⟨ F x ⟩ ⟩∘ₕ⟨ Id⟨ F f ⟩ ⟩ ⟩ c ∎
     
    
    abstract
      lawFunId₁ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ μ {i} {ε} ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ≅ id₂ Cat' {C}
      lawFunId₁ {tt} {tt} {i} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.right-id monoid)) 
        $ het-fun-ext (hcong (λ X → (λ z → Hom C ([ F i ]₀ z) ([ [ P ]₀ X ]₀ z))) (≡-to-≅ right-id))
        $ λ (c : Obj C) → hbegin
          nat-η (μ {i} {ε}) c ∘C nat-η ⟨ Id⟨ F i ⟩ ⟩∘ₕ⟨ η ⟩ c
            ≅⟨ hrefl ⟩
          nat-η (μ {i} {ε}) c ∘C (Category.id C {[ [ F i ]∘[ F ε ] ]₀ c} ∘C [ F i ]₁ (nat-η η c))
            ≅⟨ hcong (λ X → nat-η (μ {i} {ε}) c ∘C X) (≡-to-≅ $ Category.right-id C) ⟩
          nat-η (μ {i} {ε}) c ∘C [ F i ]₁ (nat-η η c)
            ≅⟨ η-left-coher ⟩
          nat-η Id⟨ F i ⟩ c ∎h
    
    abstract
      lawFunId₂ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ μ {ε} {i} ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ Id⟨ F i ⟩ ⟩ ⟩ ≅ Id⟨ F i ⟩
      lawFunId₂ {tt} {tt} {i} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.left-id monoid)) 
        $ het-fun-ext (hcong (λ X → (λ z → Hom C ([ F i ]₀ z) ([ [ P ]₀ X ]₀ z))) (≡-to-≅ left-id))
        $ λ (c : Obj C) → hbegin
          nat-η ⟨ μ {ε} {i} ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ Id⟨ F i ⟩ ⟩ ⟩ c
            ≅⟨ hrefl ⟩
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c) ∘C [ Id[ C ] ]₁ (Category.id C {[ F i ]₀ c}))
            ≅⟨ hrefl ⟩
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c) ∘C (Category.id C {[ F i ]₀ c}))
            ≅⟨ hcong (λ X → nat-η (μ {ε} {i}) c ∘C X) (≡-to-≅ $ Category.left-id C) ⟩
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c))
            ≅⟨ η-right-coher ⟩
          nat-η Id⟨ F i ⟩ c ∎h
    
    abstract
      lawFunAssoc : {w x y z : Obj monCat₁}
                  → {i : Hom monCat₁ w x} {j : Hom monCat₁ x y} {k : Hom monCat₁ y z} 
                  → ⟨ μ {k} {j ∙ i} ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ {j} {i} ⟩ ⟩ ≅ ⟨ μ {k ∙ j} {i} ⟩∘ᵥ⟨ ⟨ μ {k} {j} ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩
      lawFunAssoc {tt} {tt} {tt} {tt} {i} {j} {k} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.assoc monoid)) 
        $ het-fun-ext (hcong (λ X → (λ z → Hom C ([ M k ]₀ ([ M j ]₀ ([ M i ]₀ z))) ([ [ P ]₀ X ]₀ z))) (≡-to-≅ assoc)) 
        $ λ (c : Obj C) → hbegin
          (nat-η (μ {k} {j ∙ i}) c ∘C (idC C {[ M k ]₀ ([ M (j ∙ i) ]₀ c)} ∘C [ M k ]₁ (nat-η (μ {j} {i}) c)))
            ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {k} {j ∙ i}) c ∘C X) (Category.right-id C) ⟩
          (nat-η (μ {k} {j ∙ i}) c ∘C [ M k ]₁ (nat-η (μ {j} {i}) c))
            ≅⟨ μ-coher ⟩
          (nat-η (μ {k ∙ j} {i}) c ∘C nat-η (μ {k} {j}) ([ M i ]₀ c))
            ≅⟨ ≡-to-≅ $ cong (λ X → nat-η (μ {k ∙ j} {i}) c ∘C X) (sym (Category.left-id C)) ⟩
          (nat-η (μ {k ∙ j} {i}) c ∘C (nat-η (μ {k} {j}) ([ M i ]₀ c) ∘C (idC C {[ M k ]₀ ([ M j ]₀ ([ M i ]₀ c))})))
            ≅⟨ ≡-to-≅ $ cong (λ X → (nat-η (μ {k ∙ j} {i}) c ∘C (nat-η (μ {k} {j}) ([ M i ]₀ c) ∘C X))) (sym (Functor.id (M k))) ⟩
          (nat-η (μ {k ∙ j} {i}) c ∘C (nat-η (μ {k} {j}) ([ M i ]₀ c) ∘C [ M k ]₁ (idC C {[ M j ]₀ ([ M i ]₀ c)})))
            ≅⟨ ≡-to-≅ $ cong (λ X → (nat-η (μ {k ∙ j} {i}) c ∘C (nat-η (μ {k} {j}) ([ M i ]₀ c) ∘C [ M k ]₁ X))) (sym (Functor.id (M j))) ⟩
          (nat-η (μ {k ∙ j} {i}) c ∘C (nat-η (μ {k} {j}) ([ M i ]₀ c) ∘C [ [ M k ]∘[ M j ] ]₁ (idC C {[ M i ]₀ c}))) ∎h
