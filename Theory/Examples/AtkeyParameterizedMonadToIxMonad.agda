
module Theory.Examples.AtkeyParameterizedMonadToIxMonad where

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
open import Parameterized.IndexedMonad
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Monad
open import Theory.TwoCategory
open import Theory.TwoFunctor
open import Theory.AtkeyParameterizedMonad
open import Theory.Examples.Category
open import Theory.Examples.TwoCategory

open StrictTwoCategory
open Category 

AtkeyFunctor→IxTyCon
  : {ℓS₀ ℓS₁ : Level}
  → {S : Category {ℓS₀} {ℓS₁}}
  → (F : Functor (S op ×C S ×C setCategory {lzero}) (setCategory {lzero}))
  → (Obj S → Obj S → TyCon)
AtkeyFunctor→IxTyCon F s₁ s₂ A = [ F ]₀ (s₁ , s₂ , A)

AtkeyParameterizedMonad→IxMonad
  : {ℓS₀ ℓS₁ : Level}
  → (S : Category {ℓS₀} {ℓS₁})
  → (F : Functor (S op ×C S ×C setCategory {lzero}) (setCategory {lzero}))
  → AtkeyParameterizedMonad setCategory S F
  → IxMonad (Obj S) (AtkeyFunctor→IxTyCon F)
AtkeyParameterizedMonad→IxMonad S F monad = record
  { _>>=_ = _>>=_
  ; return = return
  ; lawIdR = lawIdR
  ; lawIdL = {!!}
  ; lawAssoc = {!!}
  } where
    SetCat = setCategory {lzero}
    M = AtkeyFunctor→IxTyCon F

    fmap : {α β : Type} {i j : Obj S}
         → (α → β) → M i j α → M i j β
    fmap {i = i} {j} f ma = [ F ]₁ (id (S op) {i} , id S {j} , f) ma
    
    join : {α : Type} {i j k : Obj S} 
         → M i j (M j k α) → M i k α
    join mma = AtkeyParameterizedMonad.μ monad mma
    
    _>>=_ : {α β : Type} {i j k : Obj S} 
          → M i j α → (α → M j k β) → M i k β
    _>>=_ ma fm = join $ fmap fm ma
    
    return : {α : Type} {i : Obj S} 
           → α → M i i α
    return a = AtkeyParameterizedMonad.η monad a
    
    open AtkeyParameterizedMonad
    
    lawIdR : {α β : Type} {i j : Obj S} 
           → (a : α) (k : α → M i j β) 
           → return a >>= k ≡ k a
    lawIdR {α} {β} {i} {j} a k = begin
      return a >>= k 
        ≡⟨ refl ⟩
      μ monad ([ F ]₁ (id (S op) {i} , id S {i} , k) (η monad a))
        ≡⟨ refl ⟩
      (μ monad ∘F ([ F ]₁ (id (S op) {i} , id S {i} , k)) ∘F (η monad)) a
        ≡⟨ cong (λ X → (μ monad ∘F X) a) (naturalη monad) ⟩
      (μ monad ∘F (η monad ∘F k)) a
        ≡⟨ refl ⟩
      ((μ monad ∘F η monad) ∘F k) a
        ≡⟨ cong (λ X → (X ∘F k) a) (AtkeyParameterizedMonad.idL monad) ⟩
      k a ∎

