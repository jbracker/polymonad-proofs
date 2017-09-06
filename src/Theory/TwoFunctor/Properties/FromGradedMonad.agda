
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
open import Haskell.Functor hiding ( functor ; functor-eq ) renaming ( Functor to HaskellFunctor )
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
open StrictTwoCategory hiding ( right-id ; left-id ; assoc )
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
                  → P₁ (Category._∘_ (HomCat monCat₂ (lift tt) (lift tt)) g f) ≡ ⟨ P₁ g ⟩∘ᵥ⟨ P₁ f ⟩
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
      μ-natural₁ : {a b c : Lift ⊤}
                 → (f : Cell₁ monCat₂ a b)
                 → {x y : Cell₁ monCat₂ b c}
                 → {α : x ≡ y}
                 → ⟨ [ P ]₁ ((monCat₂ ∘ₕ α) refl) ⟩∘ᵥ⟨ μ ⟩
                 ≡ ⟨ μ ⟩∘ᵥ⟨ ⟨ [ P ]₁ α ⟩∘ₕ⟨ [ P ]₁ refl ⟩ ⟩
      μ-natural₁ {lift tt} {lift tt} {lift tt} f {x} {y} {refl} 
        = natural-transformation-eq $ fun-ext $ λ (c : Obj Hask') → cong (λ X → nat-η μ c ∘F X) (sym (Functor.id (F x)))
      
    abstract
      μ-natural₂ : {a b c : Lift ⊤}
                 → (g : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) b c)
                 → {x y : Cell₁ (discreteHomCatTwoCategory (monoidCategory monoid)) a b}
                 → {α : x ≡ y} 
                 → ⟨ [ P ]₁ ((monCat₂ ∘ₕ refl) α) ⟩∘ᵥ⟨ μ ⟩
                 ≡ (Cat ∘ᵥ μ) ((Cat ∘ₕ [ P ]₁ refl) ([ P ]₁ α))
      μ-natural₂ {lift tt} {lift tt} {lift tt} g {x} {y} {refl}
        = natural-transformation-eq $ fun-ext $ λ (c : Obj Hask') → cong (λ X → nat-η μ c ∘F X) (sym (Functor.id (F g)))
    
    abstract
      lawFunId₁ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ≅ id₂ Cat' {Hask'}
      lawFunId₁ {lift tt} {lift tt} {i} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.right-id monoid)) 
        $ het-fun-ext (het-fun-ext hrefl (λ X → hcong (λ Y → Hom Hask ([ F i ]₀ X) ([ [ P ]₀ Y ]₀ X)) (≡-to-≅ (Monoid.right-id monoid)))) 
        $ λ (α : Type) → het-fun-ext (hcong (λ X → (λ _ → [ [ P ]₀ X ]₀ α)) (≡-to-≅ (Monoid.right-id monoid))) 
        $ λ (ma : M i α) → hbegin
          nat-η (⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩) α ma
            ≅⟨ hrefl ⟩
          fmap return ma >>= (λ x → x)
            ≅⟨ bind-arg₁ (sym right-id) (fmap return ma) (ma >>= (return ∘F return)) (hsym (law-monad-fmap return ma)) (λ x → x) ⟩
          (ma >>= (return ∘F return)) >>= (λ x → x)
            ≅⟨ hsym (law-assoc ma (return ∘F return) (λ x → x)) ⟩
          ma >>= (λ a → return (return a) >>= (λ x → x))
            ≅⟨ bind-arg₂ left-id ma (λ a → return (return a) >>= (λ x → x)) return (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Miε)) (λ a → law-left-id (return a) (λ x → x))) ⟩
          ma >>= return
            ≅⟨ law-right-id ma ⟩
          ma
            ≅⟨ hrefl ⟩
          nat-η {F = F i} (id₂ Cat' {Hask'}) α ma ∎h
    
    abstract
      lawFunId₂ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
                → ⟨ μ ⟩∘ᵥ⟨ ⟨ η ⟩∘ₕ⟨ Id⟨ F i ⟩ ⟩ ⟩ ≅ id₂ Cat'
      lawFunId₂ {lift tt} {lift tt} {i} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.left-id monoid)) 
        $ het-fun-ext (het-fun-ext hrefl (λ z → hcong (λ X → (a : M i z) → [ [ P ]₀ X ]₀ z) (≡-to-≅ (Monoid.left-id monoid)))) 
        $ λ (α : Type) → het-fun-ext (hcong (λ X → (λ _ → [ [ P ]₀ X ]₀ α)) (≡-to-≅ (Monoid.left-id monoid))) 
        $ λ (ma : M i α) → hbegin
          join (return ma)
            ≅⟨ hrefl ⟩
          return ma >>= (λ x → x)
            ≅⟨ law-left-id ma (λ x → x) ⟩
          ma
            ≅⟨ hrefl ⟩
          nat-η {F = F i} (id₂ Cat' {Hask'}) α ma ∎h
    
    abstract
      lawFunAssoc : {w x y z : Obj monCat₁}
                  → {i : Hom monCat₁ w x} {j : Hom monCat₁ x y} {k : Hom monCat₁ y z} 
                  → ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat {f = F k} ⟩∘ₕ⟨ μ ⟩ ⟩ ≅ ⟨ μ ⟩∘ᵥ⟨ ⟨ μ ⟩∘ₕ⟨ id₂ Cat {f = F i} ⟩ ⟩
      lawFunAssoc {lift tt} {lift tt} {lift tt} {lift tt} {i} {j} {k} 
        = het-natural-transformation-eq (functor-eq refl hrefl) (cong (λ X → [ P ]₀ X) (Monoid.assoc monoid)) 
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
