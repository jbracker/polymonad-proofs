
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h )

open import Extensionality
open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromHaskellIndexedMonad where

private
  SetCat' = SetCat {zero}

open Category renaming ( id to cat-id )

HaskellIndexedMonad→IndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                 → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
                                 → (Σ ({i j : Obj (Codisc Ixs)} → Hom (Codisc Ixs) i j → Functor SetCat' SetCat') (IndexedMonad (Codisc Ixs)))
HaskellIndexedMonad→IndexedMonad {ℓIxs} {Ixs} (M , monad) 
  = F , indexedMonad η μ μ-coher η-left-coher η-right-coher
  where
    open IxMonad monad
    open NaturalTransformation renaming ( η to nat-η )
    
    I = Codisc Ixs
    
    _∘I_ = _∘_ I
    
    F : {i j : Obj I} → Hom I i j → Functor SetCat' SetCat'
    F (codisc i j) = HaskellFunctor→Functor (functor j i)
    
    η : (i : Obj I) → NaturalTransformation Id[ SetCat' ] (F (cat-id I {i}))
    η i = naturalTransformation (λ α → return {α} {i}) $ λ {α β} {f} → begin
      fmap f ∘F return 
        ≡⟨ fun-ext (λ ma → sym (law-monad-fmap f (return ma))) ⟩
      (λ ma → (return ma) >>= (return ∘F f)) 
        ≡⟨ fun-ext (λ ma → law-right-id ma (return ∘F f)) ⟩
      return ∘F f ∎
    
    μ : {i j k : Obj I} → (f : Hom I i j) → (g : Hom I j k) → NaturalTransformation [ F g ]∘[ F f ] (F (g ∘I f))
    μ (codisc i j) (codisc .j k) = naturalTransformation (λ α → join {α} {k} {j} {i}) $ λ {α β} {f} → begin
      fmap f ∘F join 
        ≡⟨ refl ⟩
      (λ ma → fmap f (ma >>= id))
        ≡⟨ fun-ext (λ ma → sym (law-monad-fmap f (ma >>= id))) ⟩
      (λ ma → (ma >>= id) >>= (return ∘F f))
        ≡⟨ fun-ext (λ ma → sym (law-assoc ma id (return ∘F f))) ⟩
      (λ ma → ma >>= (λ x → x >>= (return ∘F f)))
        ≡⟨ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → sym (law-right-id (x >>= (return ∘F f)) id)))) ⟩
      (λ ma → ma >>= (λ x → return (x >>= (return ∘F f)) >>= id))
        ≡⟨ fun-ext (λ ma → law-assoc ma (λ a → return (a >>= (return ∘F f))) id) ⟩
      (λ ma → (ma >>= (λ a → return (a >>= (return ∘F f)))) >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → (ma >>= (return ∘F X)) >>= id) (fun-ext (λ x → law-monad-fmap f x))) ⟩
      (λ ma → (ma >>= (return ∘F (fmap f))) >>= id)
        ≡⟨ fun-ext (λ ma → cong (λ X → X >>= id) (law-monad-fmap (fmap f) ma)) ⟩
      (λ ma → (fmap (fmap f) ma) >>= id)
        ≡⟨ refl ⟩
      join ∘F fmap (fmap f) ∎
    
    abstract
      μ-coher : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} {x : Type}
              → nat-η (μ (g ∘I f) h) x ∘F [ F h ]₁ (nat-η (μ f g) x) 
              ≅ nat-η (μ f (h ∘I g)) x ∘F nat-η (μ g h) ([ F f ]₀ x)
      μ-coher {f = codisc i j} {codisc .j k} {codisc .k l} {α} = hbegin
        join ∘F fmap join
          ≅⟨ hrefl ⟩
        (λ ma → (fmap (λ a → a >>= id) ma) >>= id)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → cong (λ X → X >>= id) (sym (law-monad-fmap (λ a → a >>= id) ma))) ⟩
        (λ ma → (ma >>= (return ∘F (λ a → a >>= id))) >>= id)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → sym (law-assoc ma (return ∘F (λ a → a >>= id)) id)) ⟩
        (λ ma → ma >>= (λ x → return (x >>= id) >>= id))
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (x >>= id) id))) ⟩
        (λ ma → ma >>= (λ x → x >>= id))
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → law-assoc ma id id) ⟩
        (λ ma → (ma >>= id) >>= id)
          ≅⟨ hrefl ⟩
        join ∘F join ∎h
    
    abstract
      η-left-coher : {i j : Obj I} {f : Hom I i j} {x : Type}
                   → nat-η (μ (cat-id I {i}) f) x ∘F [ F f ]₁ (nat-η (η i) x) ≅ nat-η (Id⟨ F f ⟩) x
      η-left-coher {f = codisc i j} {α} = hbegin
        join ∘F fmap return
          ≅⟨ hrefl ⟩
        (λ ma → fmap return ma >>= id)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → cong (λ X → X >>= id) (sym $ law-monad-fmap return ma )) ⟩
        (λ ma → (ma >>= (return ∘F return)) >>= id)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → sym (law-assoc ma (return ∘F return) id)) ⟩
        (λ ma → ma >>= (λ x → return (return x) >>= id))
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (return x) id))) ⟩
        (λ ma → ma >>= return)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → law-left-id ma) ⟩
        id ∎h
    
    abstract
      η-right-coher : {i j : Obj I} {f : Hom I i j} {x : Type}
                    → nat-η (μ f (cat-id I {j})) x ∘F nat-η (η j) ([ F f ]₀ x) ≅ nat-η (Id⟨ F f ⟩) x
      η-right-coher {f = codisc i j} {α} = hbegin
        join ∘F return
          ≅⟨ hrefl ⟩
        (λ ma → return ma >>= id)
          ≅⟨ ≡-to-≅ $ fun-ext (λ ma → law-right-id ma id) ⟩
        id ∎h
