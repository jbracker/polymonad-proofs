
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.Graded.Monad hiding ( graded-monad )

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
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell
 
module Theory.TwoFunctor.Properties.FromGradedMonad where

open Category hiding ( right-id ; left-id ; assoc ) renaming ( id to idC )
open StrictTwoCategory
open Triple

GradedMonad→LaxTwoFunctor
  : {ℓ : Level}
  → {Effects : Set ℓ}
  → {monoid : Monoid Effects}
  → (M : Effects → TyCon)
  → (monad : GradedMonad monoid M)
  → ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory monoid)) (Cat {suc zero} {zero}) (Hask {zero})
GradedMonad→LaxTwoFunctor {ℓ} {Eff} {monoid} M monad = record
  { P₁ = λ {i} {j} → P
  ; η = λ {i} → η
  ; μ = λ {i} {j} {k} {f} {g} → μ {g} {f}
  ; laxFunId₁ = λ {x} {y} {i} → lawFunId₁ {x} {y} {i}
  ; laxFunId₂ = λ {x} {y} {i} → lawFunId₂ {x} {y} {i}
  ; laxFunAssoc = λ {w} {x} {y} {z} {i} {j} {k} → lawFunAssoc {w} {x} {y} {z} {i} {j} {k}
  ; μ-natural₁ = λ {a b c} f {x y} {α} → μ-natural₁ {a} {b} {c} f {x} {y} {α}
  ; μ-natural₂ = λ {a b c} g {x y} {α} → μ-natural₂ {a} {b} {c} g {x} {y} {α}
  }
  where
    monCat₁ = monoidCategory monoid
    monCat₂ = discreteHomCatTwoCategory monCat₁
    Cat' = Cat {suc zero} {zero}
    Hask' = Hask {zero}

    _∘Eff_ = Category._∘_ monCat₁
    
    open Monoid monoid
    open GradedMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    F = λ i → HaskellFunctor→Functor (functor i)
    
    P : Functor (HomCat monCat₂ (lift tt) (lift tt)) (HomCat Cat' Hask Hask)
    P = Functor.functor P₀ P₁ refl compose
      where
        P₀ : Obj (HomCat monCat₂ (lift tt) (lift tt)) → Obj (HomCat Cat' Hask Hask)
        P₀ i = F i
       
        P₁ : {a b : Obj (HomCat monCat₂ (lift tt) (lift tt))} → Hom (HomCat monCat₂ (lift tt) (lift tt)) a b → Hom (HomCat Cat' Hask Hask) (P₀ a) (P₀ b)
        P₁ {i} {.i} refl = Id⟨ P₀ i ⟩
        
        abstract
          compose : {a b c : Obj (HomCat monCat₂ (lift tt) (lift tt))}
                  → {f : Hom (HomCat monCat₂ (lift tt) (lift tt)) a b} {g : Hom (HomCat monCat₂ (lift tt) (lift tt)) b c}
                  → P₁ ((HomCat monCat₂ (lift tt) (lift tt) ∘ g) f) ≡ (HomCat Cat' Hask Hask ∘ P₁ g) (P₁ f)
          compose {a} {.a} {.a} {refl} {refl} = sym (Category.left-id (HomCat Cat' Hask Hask))
    
    η : NaturalTransformation Id[ Hask' ] ([ P ]₀ ε)
    η = naturalTransformation (λ α x → return {α} x) $ fun-ext $ λ a → natural a
      where
        abstract
          natural : {α β : Type} {f : α → β} → (a : α)
                  → fmap f (return a) ≡ return (f a)
          natural {α} {β} {f} a = ≅-to-≡ $ hbegin
            fmap f (return a) 
              ≅⟨ hsym (law-monad-fmap f (return a)) ⟩
            return a >>= (return ∘F f)
              ≅⟨ law-left-id a (return ∘F f) ⟩
            return (f a) ∎h
    
    μ : {i j : Eff} → NaturalTransformation ([ [ P ]₀ i ]∘[ [ P ]₀ j ]) ([ P ]₀ (i ∘Eff j))
    μ {i} {j} = naturalTransformation (λ α mma → join {α} {i} {j} mma) $ λ {α β} {f} → fun-ext $ λ mma → natural {α} {β} {f} mma 
      where
        abstract
          natural : {α β : Type} {f : α → β} → (mma : M i (M j α)) → fmap {α} {β} {i ∘Eff j} f (join {α} {i} {j} mma) ≡ join (fmap (fmap f) mma)
          natural {α} {β} {f} mma = ≅-to-≡ $ hbegin
            (M (i ∘Eff j) β          ∋ fmap f (mma >>= (λ x → x)))
              ≅⟨ hsym (law-monad-fmap f (mma >>= (λ x → x))) ⟩
            (M ((i ∘Eff j) ∘Eff ε) β ∋ (mma >>= (λ x → x)) >>= (return ∘F f))
              ≅⟨ hsym (law-assoc mma (λ z → z) (return ∘F f)) ⟩
            (M (i ∘Eff (j ∘Eff ε)) β ∋ mma >>= (λ ma → ma >>= (return ∘F f)))
              ≅⟨ bind-arg₂ right-id mma (λ ma → ma >>= (return ∘F f)) (fmap f) (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Miε)) (λ ma → law-monad-fmap f ma)) ⟩
            (M (i ∘Eff j) β          ∋ mma >>= (λ ma → fmap f ma))
              ≅⟨ bind-arg₂ (sym left-id) mma (fmap f) (λ ma → return (fmap f ma) >>= (λ x → x)) (hsym (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Mεi)) (λ ma → law-left-id (fmap f ma) (λ z → z)))) ⟩
            (M (i ∘Eff (ε ∘Eff j)) β ∋ mma >>= (λ ma → return (fmap f ma) >>= (λ x → x)))
              ≅⟨ law-assoc mma (return ∘F fmap f) (λ x → x) ⟩
            (M ((i ∘Eff ε) ∘Eff j) β ∋ (mma >>= (return ∘F fmap f)) >>= (λ x → x))
              ≅⟨ bind-arg₁ right-id (mma >>= (return ∘F fmap f)) (fmap (fmap f) mma) (law-monad-fmap (fmap f) mma) (λ x → x) ⟩ -- (law-monad-fmap (fmap f) mma)
            (M (i ∘Eff j) β          ∋ fmap {i = i} (fmap {i = j} f) mma >>= (λ x → x)) ∎h
    
    abstract
      subst-refl-id : {α : Type} {i j : Eff} → (eq : i ≡ j) → (ma : M j α) → nat-η ([ P ]₁ (subst₂ _≡_ eq refl (refl {ℓ} {Eff} {i}))) α ma ≅ nat-η (Id⟨ F j ⟩) α ma
      subst-refl-id {α} {i} {.i} refl ma = hrefl
    
    abstract
      μ-natural₁ : {a b c : Lift ⊤}
                 → (f : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) a b)
                 → {x y : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) b c}
                 → {α : x ≡ y}
                 → ⟨ [ P ]₁ ((discreteHomCatTwoCategory (monoidCategory monoid) ∘ₕ₂ α) refl) ⟩∘ᵥ⟨ μ ⟩
                 ≡ ⟨ μ ⟩∘ᵥ⟨ ⟨ [ P ]₁ α ⟩∘ₕ⟨ [ P ]₁ refl ⟩ ⟩
      μ-natural₁ {lift tt} {lift tt} {lift tt} f {x} {y} {refl} 
        = natural-transformation-eq $ fun-ext $ λ (c : Obj Hask') → cong (λ X → nat-η μ c ∘F X) (sym (Functor.id (F x)))
      
    abstract
      μ-natural₂ : {a b c : Lift ⊤}
                 → (g : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) b c)
                 → {x y : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) a b}
                 → {α : x ≡ y} 
                 → ⟨ [ P ]₁ ((discreteHomCatTwoCategory (monoidCategory monoid) ∘ₕ₂ refl) α) ⟩∘ᵥ⟨ μ ⟩
                 ≡ (Cat ∘ᵥ μ) ((Cat ∘ₕ₂ [ P ]₁ refl) ([ P ]₁ α))
      μ-natural₂ {lift tt} {lift tt} {lift tt} g {x} {y} {refl}
        = natural-transformation-eq $ fun-ext $ λ (c : Obj Hask') → cong (λ X → nat-η μ c ∘F X) (sym (Functor.id (F g)))
    
    abstract
      lawFunId₁ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ [ P ]₁ (λ' monCat₂ i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ⟩ ≡ λ' Cat' ([ P ]₀ i)
      lawFunId₁ {lift tt} {lift tt} {i} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M i α) → ≅-to-≡ $ hbegin
        nat-η (⟨ [ P ]₁ (λ' monCat₂ i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ⟩) α ma
          ≅⟨ hrefl ⟩
        (M i α                   ∋ nat-η ([ P ]₁ (λ' monCat₂ i)) α (fmap return ma >>= (λ x → x)))
          ≅⟨ subst-refl-id (sym $ hIdL₁ monCat₂ {lift tt} {lift tt} {i}) (fmap return ma >>= (λ x → x)) ⟩
        (M (i ∘Eff ε) α          ∋ nat-η (Id⟨ F (i ∘Eff ε) ⟩) α (fmap return ma >>= (λ x → x)))
          ≅⟨ hrefl ⟩
        (M (i ∘Eff ε) α          ∋ fmap return ma >>= (λ x → x))
          ≅⟨ bind-arg₁ (sym right-id) (fmap return ma) (ma >>= (return ∘F return)) (hsym (law-monad-fmap return ma)) (λ x → x) ⟩
        (M ((i ∘Eff ε) ∘Eff ε) α ∋ (ma >>= (return ∘F return)) >>= (λ x → x))
          ≅⟨ hsym (law-assoc ma (return ∘F return) (λ x → x)) ⟩
        (M (i ∘Eff (ε ∘Eff ε)) α ∋ ma >>= (λ a → return (return a) >>= (λ x → x)))
          ≅⟨ bind-arg₂ left-id ma (λ a → return (return a) >>= (λ x → x)) return (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Miε)) (λ a → law-left-id (return a) (λ x → x))) ⟩
        (M (i ∘Eff ε) α          ∋ ma >>= return) 
          ≅⟨ law-right-id ma ⟩
        (M i α                   ∋ ma)
          ≅⟨ hsym (het-cat-λ-id α ma) ⟩
        (M i α                   ∋ nat-η (λ' Cat' ([ P ]₀ i)) α ma) ∎h
    
    abstract
      lawFunId₂ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ [ P ]₁ (ρ monCat₂ i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ Id⟨ F i ⟩ ⟩ ⟩ ⟩ ≡ ρ Cat' ([ P ]₀ i)
      lawFunId₂ {lift tt} {lift tt} {i} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M i α) → ≅-to-≡ $ hbegin
        (M i α          ∋ nat-η ([ P ]₁ (ρ monCat₂ i)) α (join (return ma)))
          ≅⟨ subst-refl-id (sym $ hIdR₁ monCat₂ {lift tt} {lift tt} {i}) (join (return ma)) ⟩
        (M (ε ∘Eff i) α ∋ nat-η (Id⟨ F (ε ∘Eff i) ⟩) α (join (return ma)))
          ≅⟨ hrefl ⟩
        (M (ε ∘Eff i) α ∋ return ma >>= (λ x → x))
          ≅⟨ law-left-id ma (λ x → x) ⟩
        (M i α          ∋ ma)
          ≅⟨ hsym (het-cat-ρ-id α ma) ⟩
        (M i α          ∋ nat-η (ρ Cat' ([ P ]₀ i)) α ma) ∎h
    
    abstract
      subst-refl-id' : {α : Type} {i j : Eff} → (eq : i ≡ j) → (ma : M i α) → nat-η ([ P ]₁ (subst₂ _≡_ refl eq (refl {ℓ} {Eff} {i}))) α ma ≅ nat-η (Id⟨ F i ⟩) α ma
      subst-refl-id' {α} {i} {.i} refl ma = hrefl
    
    abstract
      lawFunAssoc : {w x y z : Obj monCat₁}
                  → {i : Hom monCat₁ w x} {j : Hom monCat₁ x y} {k : Hom monCat₁ y z} 
                  → ⟨ [ P ]₁ (α monCat₂ i j k) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ ⟩ ⟩ ⟩
                  ≡ ⟨ μ ⟩∘ᵥ⟨ ⟨ ⟨ μ ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩∘ᵥ⟨ α Cat ([ P ]₀ i) ([ P ]₀ j) ([ P ]₀ k) ⟩ ⟩
      lawFunAssoc {lift tt} {lift tt} {lift tt} {lift tt} {i} {j} {k} = natural-transformation-eq $ fun-ext $ λ (β : Type) → fun-ext $ λ (ma : M k (M j (M i β))) → ≅-to-≡ $ hbegin
        nat-η (⟨ [ P ]₁ (α monCat₂ i j k) ⟩∘ᵥ⟨ ⟨ μ {k} {j ∘Eff i} ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ {j} {i} ⟩ ⟩ ⟩) β ma
          ≅⟨ hrefl ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ nat-η ([ P ]₁ (α monCat₂ i j k)) β (join {β} {k} {j ∘Eff i} (fmap (join {β} {j} {i}) ma)))
          ≅⟨ subst-refl-id' (hAssoc₁ monCat₂ {f = i} {j} {k}) (join {β} {k} {j ∘Eff i} (fmap (join {β} {j} {i}) ma)) ⟩
        (M (k ∘Eff (j ∘Eff i)) β ∋ join {β} {k} {j ∘Eff i} (fmap (join {β} {j} {i}) ma))
          ≅⟨ hrefl ⟩
        (M (k ∘Eff (j ∘Eff i)) β ∋ fmap (join {β} {j} {i}) ma >>= (λ x → x))
          ≅⟨ bind-arg₁ (sym right-id) (fmap (join {β} {j} {i}) ma) (ma >>= (return ∘F join {β} {j} {i})) (hsym (law-monad-fmap (join {β} {j} {i}) ma)) (λ x → x) ⟩
        (M ((k ∘Eff ε) ∘Eff (j ∘Eff i)) β ∋ (ma >>= (return ∘F join {β} {j} {i})) >>= (λ x → x))
          ≅⟨ hsym (law-assoc ma (return ∘F join) (λ x → x)) ⟩
        (M (k ∘Eff (ε ∘Eff (j ∘Eff i))) β ∋ ma >>= (λ a → return (join {β} {j} {i} a) >>= (λ x → x)))
          ≅⟨ bind-arg₂ left-id ma (λ a → return (join a) >>= (λ x → x)) (λ mma → mma >>= (λ x → x)) (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Mεi)) (λ x → law-left-id (join x) (λ x → x))) ⟩
        (M (k ∘Eff (j ∘Eff i)) β ∋ ma >>= (λ mma → mma >>= (λ x → x)))
          ≅⟨ law-assoc ma (λ x → x) (λ x → x) ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ (ma >>= (λ x → x)) >>= (λ x → x))
          ≅⟨ hcong (λ X → (X ma >>= (λ x → x)) >>= (λ x → x)) (≡-to-≅ (sym (HaskellFunctor.law-id (functor k)))) ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ (fmap (λ x → x) ma >>= (λ x → x)) >>= (λ x → x))
          ≅⟨ hcong (λ X → _>>=_ (_>>=_ (fmap X ma) (λ x → x)) (λ x → x)) (≡-to-≅ (sym (HaskellFunctor.law-id (functor j)))) ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ (fmap (fmap (λ x → x)) ma >>= (λ x → x)) >>= (λ x → x))
          ≅⟨ hrefl ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ join {β} {k ∘Eff j} {i} (join {M i β} {k} {j} (fmap (fmap (λ x → x)) ma)))
          ≅⟨ hcong (λ X → join {β} {k ∘Eff j} {i} (join {M i β} {k} {j} (fmap (fmap (λ x → x)) X))) (hsym (het-cat-α-id {F = [ P ]₀ i} {[ P ]₀ j} {[ P ]₀ k} β ma)) ⟩
        (M ((k ∘Eff j) ∘Eff i) β ∋ join {β} {k ∘Eff j} {i} (join {M i β} {k} {j} (fmap (fmap (λ x → x)) (nat-η (α Cat ([ P ]₀ i) ([ P ]₀ j) ([ P ]₀ k)) β ma))))
          ≅⟨ hrefl ⟩
        nat-η (⟨ μ {k ∘Eff j} {i} ⟩∘ᵥ⟨ ⟨ ⟨ μ {k} {j} ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩∘ᵥ⟨ α Cat ([ P ]₀ i) ([ P ]₀ j) ([ P ]₀ k) ⟩ ⟩) β ma ∎h
