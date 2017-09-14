
open import Level
open import Function renaming ( _∘_ to _∘F_ )

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
  → (M : Mon → Functor C C)
  → (monad : GradedMonad monoid M)
  → ConstLaxTwoFunctor (monoidTwoCategory monoid) (Cat {ℓC₀} {ℓC₁}) C
GradedMonad→LaxTwoFunctor {ℓMon} {ℓC₀} {ℓC₁} {C} {Mon} {monoid} M monad = record
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
            ≡⟨ nat-eq (vertical-right-id Cat') ⟩
          nat-η (μ {x} {f}) c
            ≡⟨ nat-eq (sym $ vertical-left-id Cat') ⟩
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
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c) ∘C [ {!!} ]₁ (Category.id C {[ F i ]₀ c}))
            ≅⟨ {!!} ⟩ -- hcong (λ X → nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c) ∘C X)) (≡-to-≅ $ Functor.id {!!}) ⟩
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c) ∘C Category.id C {{!!}})
            ≅⟨ hcong (λ X → nat-η (μ {ε} {i}) c ∘C X) (≡-to-≅ $ Category.left-id C) ⟩
          nat-η (μ {ε} {i}) c ∘C (nat-η η ([ F i ]₀ c))
            ≅⟨ η-right-coher ⟩
          nat-η Id⟨ F i ⟩ c ∎h
    
    abstract
      lawFunAssoc : {w x y z : Obj monCat₁}
                  → {i : Hom monCat₁ w x} {j : Hom monCat₁ x y} {k : Hom monCat₁ y z} 
                  → ⟨ μ {k} {j ∙ i} ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ {j} {i} ⟩ ⟩ ≅ ⟨ μ {k ∙ j} {i} ⟩∘ᵥ⟨ ⟨ μ {k} {j} ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩
      lawFunAssoc {tt} {tt} {tt} {tt} {i} {j} {k} 
        = {!!} {- het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.assoc monoid)) 
        $ het-fun-ext (hcong (λ X → (λ z → (a : M k (M j (M i z))) → [ [ P ]₀ X ]₀ z)) (≡-to-≅ (Monoid.assoc monoid))) 
        $ λ (β : Type) → het-fun-ext (hcong (λ X → (λ _ → [ [ P ]₀ X ]₀ β)) (≡-to-≅ (Monoid.assoc monoid))) 
        $ λ (ma : M k (M j (M i β))) → hbegin
          nat-η (⟨ μ {k} {j ∘Eff i} ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ {j} {i} ⟩ ⟩) β ma
            ≅⟨ hrefl ⟩
          join {β} {k} {j ∘Eff i} (fmap (join {β} {j} {i}) ma)
            ≅⟨ hrefl ⟩
          fmap (join {β} {j} {i}) ma >>= (λ x → x)
            ≅⟨ bind-arg₁ (sym right-id) (fmap (join {β} {j} {i}) ma) (ma >>= (return ∘F join {β} {j} {i})) (hsym (law-monad-fmap (join {β} {j} {i}) ma)) (λ x → x) ⟩
          (ma >>= (return ∘F join {β} {j} {i})) >>= (λ x → x)
            ≅⟨ hsym (law-assoc ma (return ∘F join) (λ x → x)) ⟩
          ma >>= (λ a → return (join {β} {j} {i} a) >>= (λ x → x))
            ≅⟨ bind-arg₂ left-id ma (λ a → return (join a) >>= (λ x → x)) (λ mma → mma >>= (λ x → x)) (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Mεi)) (λ x → law-left-id (join x) (λ x → x))) ⟩
          ma >>= (λ mma → mma >>= (λ x → x))
            ≅⟨ law-assoc ma (λ x → x) (λ x → x) ⟩
          (ma >>= (λ x → x)) >>= (λ x → x)
            ≅⟨ hcong (λ X → (X ma >>= (λ x → x)) >>= (λ x → x)) (≡-to-≅ (sym (HaskellFunctor.law-id (functor k)))) ⟩
          (fmap (λ x → x) ma >>= (λ x → x)) >>= (λ x → x)
            ≅⟨ hcong (λ X → _>>=_ (_>>=_ (fmap X ma) (λ x → x)) (λ x → x)) (≡-to-≅ (sym (HaskellFunctor.law-id (functor j)))) ⟩
          (fmap (fmap (λ x → x)) ma >>= (λ x → x)) >>= (λ x → x)
            ≅⟨ hrefl ⟩
          join {β} {k ∘Eff j} {i} (join {M i β} {k} {j} (fmap (fmap (λ x → x)) ma))
            ≅⟨ hrefl ⟩
          nat-η (⟨ μ {k ∘Eff j} {i} ⟩∘ᵥ⟨ ⟨ μ {k} {j} ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩) β ma ∎h
-}
