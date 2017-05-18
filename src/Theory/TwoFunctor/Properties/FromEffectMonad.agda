
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
open import Haskell.Parameterized.EffectMonad

open import Theory.Triple
open import Theory.Monoid
open import Theory.Category hiding ( category )
open import Theory.Category.Examples
open import Theory.Functor hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoCategory.Examples.DiscreteHomCat
open import Theory.TwoFunctor
open import Theory.TwoFunctor.ConstZeroCell
 
module Theory.TwoFunctor.Properties.FromEffectMonad where

open Category hiding ( right-id ; left-id ; assoc )
open StrictTwoCategory
open Triple

EffectMonad→LaxTwoFunctor
  : {ℓ : Level}
  → (Effects : Set ℓ)
  → (monoid : Monoid Effects)
  → (M : Effects → TyCon)
  → (monad : EffectMonad monoid M)
  → ConstLaxTwoFunctor (discreteHomCatTwoCategory (monoidCategory monoid)) (Cat {suc zero} {zero}) (Hask {zero})
EffectMonad→LaxTwoFunctor {ℓ} Eff monoid M monad = record
  { P₁ = λ {i} {j} → P
  ; η = λ {i} → η
  ; μ = λ {i} {j} {k} {f} {g} → μ {g} {f}
  ; laxFunId₁ = λ {i} {j} {f} → lawFunId₁ {i} {j} {f}
  ; laxFunId₂ = λ {i} {j} {f} → {!!}
  ; laxFunAssoc = λ {i} {j} {k} {l} {f} {g} {h} → {!!}
  }
  where
    monCat₁ = monoidCategory monoid
    monCat₂ = discreteHomCatTwoCategory monCat₁
    Cat' = Cat {suc zero} {zero}
    Hask' = Hask {zero}

    --ε = Monoid.ε monoid

    _∘Eff_ = Category._∘_ monCat₁
    
    open Monoid monoid
    open EffectMonad monad
    open NaturalTransformation renaming ( η to nat-η ; natural to nat-natural )
    
    F = λ i → HaskellFunctor→Functor (functor i)
    
    P : Functor (HomCat monCat₂ (lift tt) (lift tt)) (HomCat Cat' Hask Hask)
    P = Functor.functor P₀ P₁ refl compose
      where
        P₀ : Obj (HomCat monCat₂ (lift tt) (lift tt)) → Obj (HomCat Cat' Hask Hask)
        P₀ i = F i
       
        P₁ : {a b : Obj (HomCat monCat₂ (lift tt) (lift tt))} → Hom (HomCat monCat₂ (lift tt) (lift tt)) a b → Hom (HomCat Cat' Hask Hask) (P₀ a) (P₀ b)
        P₁ {i} {.i} refl = Id⟨ P₀ i ⟩
        
        compose : {a b c : Obj (HomCat monCat₂ (lift tt) (lift tt))}
                → {f : Hom (HomCat monCat₂ (lift tt) (lift tt)) a b} {g : Hom (HomCat monCat₂ (lift tt) (lift tt)) b c}
                → P₁ ((HomCat monCat₂ (lift tt) (lift tt) ∘ g) f) ≡ (HomCat Cat' Hask Hask ∘ P₁ g) (P₁ f)
        compose {a} {.a} {.a} {refl} {refl} = refl
    
    η : NaturalTransformation Id[ Hask' ] ([ P ]₀ ε)
    η = naturalTransformation (λ α x → return {α} x) $ fun-ext $ λ a → natural a
      where
        natural : {α β : Type} {f : α → β} → (a : α)
                → fmap f (return a) ≡ return (f a)
        natural {α} {β} {f} a = ≅-to-≡ $ hbegin
          fmap f (return a) 
            ≅⟨ hsym (law-monad-fmap f (return a)) ⟩
          return a >>= (return ∘F f)
            ≅⟨ law-left-id a (return ∘F f) ⟩
          return (f a) ∎h
    
    bind-arg-1 : {α β : Type} {i j k : Eff} → i ≡ j → (ma : M i α) → (mb : M j α) → ma ≅ mb → (f : α → M k β) → ma >>= f ≅ mb >>= f
    bind-arg-1 refl ma .ma hrefl f = hrefl

    bind-arg-2 : {α β : Type} {i j k : Eff} → j ≡ k → (ma : M i α) → (f : α → M j β) → (g : α → M k β) → f ≅ g → ma >>= f ≅ ma >>= g
    bind-arg-2 refl ma f .f hrefl = hrefl
    
    μ : {i j : Eff} → NaturalTransformation ([ [ P ]₀ i ]∘[ [ P ]₀ j ]) ([ P ]₀ (i ∘Eff j))
    μ {i} {j} = naturalTransformation (λ α mma → join {α} {i} {j} mma) $ λ {α β} {f} → fun-ext $ λ mma → natural {α} {β} {f} mma 
      where
        natural : {α β : Type} {f : α → β} → (mma : M i (M j α)) → fmap {α} {β} {i ∘Eff j} f (join {α} {i} {j} mma) ≡ join (fmap (fmap f) mma)
        natural {α} {β} {f} mma = ≅-to-≡ $ hbegin
          (M (i ∘Eff j) β          ∋ fmap f (mma >>= (λ x → x)))
            ≅⟨ hsym (law-monad-fmap f (mma >>= (λ x → x))) ⟩
          (M ((i ∘Eff j) ∘Eff ε) β ∋ (mma >>= (λ x → x)) >>= (return ∘F f))
            ≅⟨ hsym (law-assoc mma (λ z → z) (return ∘F f)) ⟩
          (M (i ∘Eff (j ∘Eff ε)) β ∋ mma >>= (λ ma → ma >>= (return ∘F f)))
            ≅⟨ bind-arg-2 right-id mma (λ ma → ma >>= (return ∘F f)) (fmap f) (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Miε)) (λ ma → law-monad-fmap f ma)) ⟩
          (M (i ∘Eff j) β          ∋ mma >>= (λ ma → fmap f ma))
            ≅⟨ bind-arg-2 (sym left-id) mma (fmap f) (λ ma → return (fmap f ma) >>= (λ x → x)) (hsym (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Mεi)) (λ ma → law-left-id (fmap f ma) (λ z → z)))) ⟩
          (M (i ∘Eff (ε ∘Eff j)) β ∋ mma >>= (λ ma → return (fmap f ma) >>= (λ x → x)))
            ≅⟨ law-assoc mma (return ∘F fmap f) (λ x → x) ⟩
          (M ((i ∘Eff ε) ∘Eff j) β ∋ (mma >>= (return ∘F fmap f)) >>= (λ x → x))
            ≅⟨ bind-arg-1 right-id (mma >>= (return ∘F fmap f)) (fmap (fmap f) mma) (law-monad-fmap (fmap f) mma) (λ x → x) ⟩ -- (law-monad-fmap (fmap f) mma)
          (M (i ∘Eff j) β          ∋ fmap {i = i} (fmap {i = j} f) mma >>= (λ x → x)) ∎h
    
    helper1 : {α : Type} {i : Eff} → (ma : M (i ∘Eff ε) α) → nat-η ([ P ]₁ (λ' monCat₂ i)) α ma ≅ nat-η (Id⟨ F (i ∘Eff ε) ⟩) α ma
    helper1 {α} {i} ma = {!!}
    
    lawFunId₁ : {x y : Obj monCat₁} {i : Hom monCat₁ x y} 
              → ⟨ [ P ]₁ (λ' monCat₂ i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ⟩ ≡ λ' Cat' ([ P ]₀ i)
    lawFunId₁ {lift tt} {lift tt} {i} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M i α) → ≅-to-≡ $ hbegin
      nat-η (⟨ [ P ]₁ (λ' monCat₂ i) ⟩∘ᵥ⟨ ⟨ μ ⟩∘ᵥ⟨ ⟨ id₂ Cat' {f = F i} ⟩∘ₕ⟨ η ⟩ ⟩ ⟩) α ma
        ≅⟨ hrefl ⟩
      (M i α ∋ nat-η ([ P ]₁ (λ' monCat₂ i)) α (fmap return ma >>= (λ x → x)))
        ≅⟨ helper1 (fmap return ma >>= (λ x → x)) ⟩
      (M (i ∘Eff ε) α ∋ nat-η (Id⟨ F (i ∘Eff ε) ⟩) α (fmap return ma >>= (λ x → x)))
        ≅⟨ hrefl ⟩
      (M (i ∘Eff ε) α ∋ fmap return ma >>= (λ x → x))
        ≅⟨ bind-arg-1 (sym right-id) (fmap return ma) (ma >>= (return ∘F return)) (hsym (law-monad-fmap return ma)) (λ x → x) ⟩
      (M ((i ∘Eff ε) ∘Eff ε) α ∋ (ma >>= (return ∘F return)) >>= (λ x → x))
        ≅⟨ hsym (law-assoc ma (return ∘F return) (λ x → x)) ⟩
      (M (i ∘Eff (ε ∘Eff ε)) α ∋ ma >>= (λ a → return (return a) >>= (λ x → x)))
        ≅⟨ bind-arg-2 left-id ma (λ a → return (return a) >>= (λ x → x)) return (het-fun-ext (het-fun-ext hrefl (λ _ → hsym Mi≅Miε)) (λ a → law-left-id (return a) (λ x → x))) ⟩
      (M (i ∘Eff ε) α ∋ ma >>= return) 
        ≅⟨ law-right-id ma ⟩
      (M i α ∋ ma) ∎h
    {-
    
    lawFunId₂ : {i j : Ixs}-- tt =  ρ Ixs₂ (lift tt)
              → ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩∘ᵥ⟨ ⟨ μ {i} {j} {j} ⟩∘ᵥ⟨ ⟨ η {j} ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩ ⟩ ⟩ ≡ ρ Cat' ([ P {i} {j} ]₀ (lift tt))
    lawFunId₂ {i} {j} = natural-transformation-eq $ fun-ext $ λ (α : Type) → fun-ext $ λ (ma : M j i α) → begin
      join (return ma)
        ≡⟨⟩
      return ma >>= (λ x → x)
        ≡⟨ law-right-id ma (λ x → x) ⟩
      ma
        ≡⟨ sym (≅-to-≡ (het-cat-ρ-id {F = [ P {i} {j} ]₀ (lift tt)} α ma)) ⟩
      (nat-η (ρ Cat' ([ P {i} {j} ]₀ (lift tt))) α) ma ∎

    lawFunAssoc : {i j k l : Ixs}
                → ⟨ Id⟨ [ P {i} {l} ]₀ (lift tt) ⟩ ⟩∘ᵥ⟨ ⟨ μ {i} {k} {l} ⟩∘ᵥ⟨ ⟨ Id⟨ [ P {k} {l} ]₀ (lift tt) ⟩ ⟩∘ₕ⟨ μ {i} {j} {k} ⟩ ⟩ ⟩
                ≡ ⟨ μ {i} {j} {l} ⟩∘ᵥ⟨ ⟨ ⟨ μ {j} {k} {l} ⟩∘ₕ⟨ Id⟨ [ P {i} {j} ]₀ (lift tt) ⟩ ⟩ ⟩∘ᵥ⟨ α Cat' ([ P {i} {j} ]₀ (lift tt)) ([ P {j} {k} ]₀ (lift tt)) ([ P {k} {l} ]₀ (lift tt)) ⟩ ⟩
    lawFunAssoc {i} {j} {k} {l} = natural-transformation-eq $ fun-ext $ λ (A : Type) → fun-ext $ λ (ma : M l k (M k j (M j i A))) → begin
      join {A} {l} {k} {i} (fmap (join {A} {k} {j} {i}) ma)
        ≡⟨⟩
      fmap (join {A} {k} {j} {i}) ma >>= (λ x → x)
        ≡⟨ cong (λ X → X >>= (λ x → x)) (sym (law-monad-fmap join ma)) ⟩
      (ma >>= (return ∘F join {A} {k} {j} {i})) >>= (λ x → x)
        ≡⟨ sym (law-assoc ma (return ∘F join) (λ x → x)) ⟩
      ma >>= (λ mma → return (join {A} {k} {j} {i} mma) >>= (λ x → x))
        ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ mma → law-right-id (join mma) (λ x → x))) ⟩
      ma >>= (λ mma → mma >>= (λ x → x))
        ≡⟨ cong (λ X → X ma >>= (λ mma → mma >>= (λ x → x))) (sym (Functor.law-id (functor l k))) ⟩
      fmap (λ x → x) ma >>= (λ ma → ma >>= (λ x → x))
        ≡⟨ cong (λ X → fmap X ma >>= (λ mma → mma >>= (λ x → x))) (sym (Functor.law-id (functor k j))) ⟩
      fmap (fmap (λ x → x)) ma >>= (λ ma → ma >>= (λ x → x))
        ≡⟨ law-assoc (fmap (fmap (λ x → x)) ma) (λ x → x) (λ x → x) ⟩
      (fmap (fmap (λ x → x)) ma >>= (λ x → x)) >>= (λ x → x)
        ≡⟨⟩
      join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) ma))
        ≡⟨ cong (λ X → join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) X))) (sym (≅-to-≡ (het-cat-α-id {F = [ P {i} {j} ]₀ (lift tt)} {[ P {j} {k} ]₀ (lift tt)} {[ P {k} {l} ]₀ (lift tt)} A ma))) ⟩
      join {A} {l} {j} {i} (join {M j i A} {l} {k} {j} (fmap (fmap (λ x → x)) ((nat-η (α Cat' ([ P {i} {j} ]₀ (lift tt)) ([ P {j} {k} ]₀ (lift tt)) ([ P {k} {l} ]₀ (lift tt))) A) ma))) ∎
-}
