
module Theory.Examples.IxMonadToAtkeyParameterizedMonad where

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
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Utilities
open import Haskell
open import Haskell.Parameterized.IndexedMonad
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation
open import Theory.Monad hiding ( monad )
open import Theory.TwoCategory
open import Theory.TwoFunctor
open import Theory.Monad.Atkey
open import Theory.Examples.Category
open import Theory.Examples.TwoCategory

open StrictTwoCategory
open Category 

IxMonad→AtkeyFunctor
  : {ℓS₀ ℓS₁ : Level}
  → (S : Category {ℓS₀} {ℓS₁})
  → (M : Obj S → Obj S → TyCon)
  → IxMonad (Obj S) M 
  → Functor (S op ×C S ×C setCategory {lzero}) (setCategory {lzero})
IxMonad→AtkeyFunctor S M monad = record 
  { F₀ = F₀
  ; F₁ = F₁
  ; id = {!!}
  ; compose = {!!}
  } where
    C = setCategory {lzero}
    
    _>>=_ = IxMonad._>>=_ monad
    return = IxMonad.return monad
    join = IxMonad.join monad

    fmap : {i j : Obj S} {a b : Type} → (a → b) → M i j a → M i j b
    fmap f ma = ma >>= (return ∘F f)
    
    F₀ : Obj (S op ×C S ×C C) → Obj C
    F₀ (s₁ , s₂ , T) = M s₁ s₂ T
    
    F₁ : {a b : Obj (S op ×C S ×C C)} → Hom (S op ×C S ×C C) a b → Hom C (F₀ a) (F₀ b)
    F₁ (sf₁ , sf₂ , f) ma = {!!}

    idFunc : {a : Obj (S op ×C S ×C C)} 
           → F₁ (id (S op ×C S ×C C) {a}) ≡ id C
    idFunc {s , s' , x} = begin
      F₁ (id (S op ×C S ×C C) {s , s' , x}) 
        ≡⟨ {!!} ⟩
      id C ∎
    

IxMonad→AtkeyParameterizedMonad 
  : {ℓS₀ ℓS₁ : Level}
  → (S : Category {ℓS₀} {ℓS₁}) 
  → (M : Obj S → Obj S → TyCon)
  → (monad : IxMonad (Obj S) M) 
  → AtkeyParameterizedMonad setCategory S (IxMonad→AtkeyFunctor S M monad)
IxMonad→AtkeyParameterizedMonad S M monad = record
  { η = return
  ; μ = join
  ; naturalη = {!!}
  ; dinaturalη = {!!}
  ; naturalμ = {!!}
  ; naturalμ₁ = {!!}
  ; naturalμ₂ = {!!}
  ; dinaturalμ = {!!}
  ; assoc = {!!}
  ; left-id = {!!}
  ; right-id = {!!}
  } where
    join = IxMonad.join monad
    return = IxMonad.return monad
    
    assocAtkey : {x : Obj setCategory} {s₀ s₁ s₂ s₃ : Obj S} 
               → join {x} {s₀} {s₁} {s₃} ∘F ([ IxMonad→AtkeyFunctor S M monad ]₁ (id S , id S , join {x} {s₁} {s₂} {s₃}))
               ≡ join {x} {s₀} {s₂} {s₃} ∘F join {M s₂ s₃ x} {s₀} {s₁} {s₂}
    assocAtkey {x} {s₀} {s₁} {s₂} {s₃} = begin
      join {x} {s₀} {s₁} {s₃} ∘F ([ IxMonad→AtkeyFunctor S M monad ]₁ (id S , id S , join {x} {s₁} {s₂} {s₃}))
        ≡⟨ {!!} ⟩
      join {x} {s₀} {s₂} {s₃} ∘F join {M s₂ s₃ x} {s₀} {s₁} {s₂} ∎
