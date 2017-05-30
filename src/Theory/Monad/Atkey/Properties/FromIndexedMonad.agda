
module Theory.Monad.Atkey.Properties.FromIndexedMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Utilities
open import Extensionality
open import Haskell
open import Haskell.Functor renaming ( Functor to HaskFunctor )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Monad.Definition hiding ( monad )
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.Definition
open import Theory.Monad.Atkey
open import Theory.Category.Examples
open import Theory.TwoCategory.Examples

open StrictTwoCategory
open Category 
open Triple

IxTyCon→AtkeyFunctor
  : {ℓ : Level}
  → (Ixs : Set ℓ)
  → (M : Obj ((discreteCategory Ixs) op) → Obj (discreteCategory Ixs) → TyCon)
  → (monad : IxMonad Ixs M)
  → (Functor ((discreteCategory Ixs) op ×C (discreteCategory Ixs) ×C Hask {lzero}) (Hask {lzero}))
IxTyCon→AtkeyFunctor Ixs M monad = functor F₀ F₁ (λ {a} → law-id {a}) (λ {a} {b} {c} {f} {g} → law-compose {a} {b} {c} {f} {g})
  where
    S = discreteCategory Ixs
    H = Hask {lzero}
    _∘SSH_ = Category._∘_ (S op ×C S ×C H)
    _∘S_ = Category._∘_ S
    _∘Sop_ = Category._∘_ (S op)
    
    F₀ : Obj ((S op) ×C S ×C H) → Obj H
    F₀ (s₀ , s₁ , a) = M s₀ s₁ a
    
    F₁ : {a b : Obj ((S op) ×C S ×C H)} → Hom ((S op) ×C S ×C H) a b → Hom H (F₀ a) (F₀ b)
    F₁ {sa₀ , sa₁ , a} {.sa₀ , .sa₁ , b} (refl , refl , f) ma = IxMonad.fmap monad f ma
    
    law-id : {a : Obj ((S op) ×C S ×C H)} → IxMonad.fmap monad (id H) ≡ id H
    law-id {s₀ , s₁ , α} = Functor.law-id (IxMonad.functor monad s₀ s₁)

    law-compose : {a b c : Obj ((S op) ×C S ×C H)}
                → {f : Hom ((S op) ×C S ×C H) a b}
                → {g : Hom ((S op) ×C S ×C H) b c}
                → F₁ (g ∘SSH f) ≡ F₁ g ∘F F₁ f
    law-compose {a₀ , a₁ , α} {f = refl , refl , f} {refl , refl , g} = Functor.law-compose (IxMonad.functor monad a₀ a₁) g f

IxMonad→AtkeyParameterizedMonad
  : {ℓ : Level}
  → (Ixs : Set ℓ)
  → (M : Obj ((discreteCategory Ixs) op) → Obj (discreteCategory Ixs) → TyCon)
  → (monad : IxMonad Ixs M)
  → AtkeyParameterizedMonad setCategory (discreteCategory Ixs)
IxMonad→AtkeyParameterizedMonad Ixs M monad = record
  { T = T
  ; η = return
  ; μ = join
  ; naturalη = λ {s} {a} {b} {f} → naturalη {s} {a} {b} {f}
  ; dinaturalη = λ {x} {a} {b} {f} → dinaturalη {x} {a} {b} {f}
  ; naturalμ = λ {s₀} {s₁} {s₂} {a} {b} {f} → naturalμ {s₀} {s₁} {s₂} {a} {b} {f}
  ; naturalμ₁ = λ {s₀} {s₁} {x} {a} {b} {f} → naturalμ₁ {s₀} {s₁} {x} {a} {b} {f}
  ; naturalμ₂ = λ {s₀} {s₁} {x} {a} {b} {f} → naturalμ₂ {s₀} {s₁} {x} {a} {b} {f}
  ; dinaturalμ = λ {s₀} {s₁} {x} {a} {b} {f} → dinaturalμ {s₀} {s₁} {x} {a} {b} {f}
  ; assoc = λ {x} {s₀} {s₁} {s₂} {s₃} → assoc' {x} {s₀} {s₁} {s₂} {s₃}
  ; left-id = λ {x} {s₁} {s₂} → left-id' {x} {s₁} {s₂}
  ; right-id = λ {x} {s₁} {s₂} → right-id' {x} {s₁} {s₂}
  } where
    T = IxTyCon→AtkeyFunctor Ixs M monad
    S = discreteCategory Ixs
    
    open IxMonad monad hiding ( bind )
    
    naturalη : {s : Ixs} {a b : Type} {f : Hom Hask a b} 
             → IxMonad.fmap monad f ∘F return ≡ return ∘F f
    naturalη {s} {f = f} = fun-ext $ λ x → begin
      fmap f (return x)
        ≡⟨ sym (law-monad-fmap f (return x)) ⟩
      return x >>= (return ∘F f)
        ≡⟨ law-right-id x (return ∘F f) ⟩
      return (f x) ∎
    
    dinaturalη : {x : Type} {a b : Ixs} {f : Hom S a b} 
               → [ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (refl , f , (λ x → x)) ∘F return
               ≡ [ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (f , refl , (λ x → x)) ∘F return
    dinaturalη {f = refl} = refl
    
    naturalμ : {s₁ s₂ s₃ : Ixs} {a b : Type} {f : Hom Hask a b} 
             → fmap f ∘F join ≡ join ∘F fmap (fmap f)
    naturalμ {f = f} = fun-ext $ λ mma → begin
      fmap f (join mma) 
        ≡⟨ sym (law-monad-fmap f (join mma)) ⟩ 
      (mma >>= (λ x → x)) >>= (return ∘F f)
        ≡⟨ sym (law-assoc mma (λ x → x) (return ∘F f)) ⟩ 
      mma >>= (λ ma → ma >>= (return ∘F f))
        ≡⟨ cong (λ X → mma >>= X) (fun-ext (λ ma → sym (law-right-id (ma >>= (return ∘F f)) (λ x → x)))) ⟩ 
      mma >>= (λ ma → (return (ma >>= (return ∘F f))) >>= (λ x → x))
        ≡⟨ law-assoc mma (return ∘F (λ ma → ma >>= (return ∘F f))) (λ x → x) ⟩ 
      (mma >>= (return ∘F (λ ma → ma >>= (return ∘F f)))) >>= (λ x → x)
        ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (law-monad-fmap (λ ma → ma >>= (return ∘F f)) mma) ⟩ 
      join (fmap (λ ma → ma >>= (return ∘F f)) mma)
        ≡⟨ cong (λ X → join (fmap X mma)) (fun-ext (λ ma → law-monad-fmap f ma)) ⟩ 
      join (fmap (fmap f) mma) ∎

    naturalμ₁ : {s₂ s₃ : Ixs} {x : Type} {a b : Ixs} {f : Hom (S op) a b} 
              → [ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (f , refl , (λ x → x)) ∘F join
              ≡ join ∘F ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (f , refl , fmap (λ x → x)))
    naturalμ₁ {f = refl} = naturalμ {f = λ x → x}
    
    naturalμ₂ : {s₁ s₂ : Ixs} {x : Type} {a b : Ixs} {f : Hom S a b} 
              → ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (refl , f , (λ x → x))) ∘F join
              ≡ join ∘F (fmap ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (refl , f , (λ x → x))))
    naturalμ₂ {f = refl} = naturalμ {f = λ x → x}

    dinaturalμ : {s₁ s₃ : Ixs} {x : Type} {a b : Ixs} {f : Hom S a b} 
               → join ∘F (fmap ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (f , refl , (λ x → x))))
               ≡ join ∘F ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (refl , f , fmap (λ x → x)))
    dinaturalμ {f = refl} = refl
    
    assoc' : {x : Type} {s₀ s₁ s₂ s₃ : Ixs} 
           → join ∘F (fmap join) ≡ join ∘F join
    assoc' = fun-ext $ λ mma → begin
      fmap (λ ma → ma >>= (λ x → x)) mma >>= (λ x → x) 
        ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (sym (law-monad-fmap (λ ma → ma >>= (λ x → x)) mma)) ⟩ 
      (mma >>= (λ ma → return (ma >>= (λ x → x)))) >>= (λ x → x) 
        ≡⟨ sym (law-assoc mma (λ ma → return (ma >>= (λ x → x))) (λ x → x)) ⟩ 
      mma >>= (λ ma → return (ma >>= (λ x → x)) >>= (λ x → x))
        ≡⟨ cong (λ X → _>>=_ mma X) (fun-ext (λ ma → law-right-id (ma >>= (λ x → x)) (λ x → x))) ⟩  
      mma >>= (λ ma → ma >>= (λ x → x))
        ≡⟨ law-assoc mma (λ x → x) (λ x → x) ⟩ 
      (mma >>= (λ x → x)) >>= (λ x → x) ∎

    left-id' : {x : Type} {s₁ s₂ : Ixs} → join ∘F (fmap return) ≡ (λ x → x)
    left-id' = fun-ext $ λ mma → begin
      (fmap return mma) >>= (λ x → x) 
        ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (sym (law-monad-fmap return mma)) ⟩ 
      (mma >>= (return ∘F return)) >>= (λ x → x) 
        ≡⟨ sym (law-assoc mma (return ∘F return) (λ x → x)) ⟩ 
      mma >>= (λ ma → return (return ma) >>= (λ x → x)) 
        ≡⟨ cong (λ X → _>>=_ mma X) (fun-ext (λ ma → law-right-id (return ma) (λ x → x))) ⟩ 
      mma >>= return
        ≡⟨ law-left-id mma ⟩ 
      mma ∎
    
    right-id' : {x : Type} {s₁ s₂ : Ixs} → join ∘F return ≡ (λ x → x)
    right-id' = fun-ext $ λ ma → law-right-id ma (λ x → x)
