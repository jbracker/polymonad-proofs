
module Theory.Monad.Atkey.IsIxMonad where

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
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ )
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
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  } where
    SetCat = setCategory {lzero}
    M = AtkeyFunctor→IxTyCon F

    _∘S_ = _∘_ S
    _∘Sop_ = _∘_ (S op)

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
    
    law-right-id : {α β : Type} {i j : Obj S} 
           → (a : α) (k : α → M i j β) 
           → return a >>= k ≡ k a
    law-right-id {α} {β} {i} {j} a k = begin
      return a >>= k 
        ≡⟨ refl ⟩
      μ monad ([ F ]₁ (id (S op) {i} , id S {i} , k) (η monad a))
        ≡⟨ refl ⟩
      (μ monad ∘F ([ F ]₁ (id (S op) {i} , id S {i} , k)) ∘F (η monad)) a
        ≡⟨ cong (λ X → (μ monad ∘F X) a) (naturalη monad) ⟩
      (μ monad ∘F (η monad ∘F k)) a
        ≡⟨ refl ⟩
      (μ monad ∘F η monad) (k a)
        ≡⟨ cong (λ X → X (k a)) (AtkeyParameterizedMonad.right-id monad) ⟩
      k a ∎
    
    law-left-id : {α : Type} {i j : Obj S}
           → (m : M i j α) 
           → m >>= return ≡ m
    law-left-id {α} {i} {j} m = begin
      m >>= return 
        ≡⟨ refl ⟩
      (μ monad ∘F [ F ]₁ (id (S op) {i} , id S {j} , η monad)) m
        ≡⟨ cong (λ X →  X m) (AtkeyParameterizedMonad.left-id monad) ⟩
      m ∎

    law-assoc : {α β γ : Type} {i j k l : Obj S}
             → (m : M i j α) (f : α → M j k β) (g : β → M k l γ) 
             → m >>= (λ x → f x >>= g) ≡ (m >>= f) >>= g
    law-assoc m f g = begin
      m >>= (λ x → f x >>= g) 
        ≡⟨ refl ⟩
      (μ monad ∘F ([ F ]₁ ( id (S op) , id S , (μ monad ∘F ([ F ]₁ (id (S op) , id S , g)) ∘F f)) ) ) m
        ≡⟨ cong₂ (λ X Y → (μ monad ∘F ([ F ]₁ (X , Y , (μ monad ∘F ([ F ]₁ (id (S op) , id S , g)) ∘F f)) ) ) m) (sym $ Category.left-id (S op)) (sym $ Category.left-id S) ⟩
      (μ monad ∘F ([ F ]₁ ( (id (S op) ∘Sop id (S op)) , (id S ∘S id S) , (μ monad ∘F ([ F ]₁ (id (S op) , id S , g)) ∘F f)) ) ) m
        ≡⟨ cong (λ X → (μ monad ∘F X) m) (Functor.compose F) ⟩
      (μ monad ∘F ([ F ]₁ ( id (S op) , id S , μ monad ) ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g) ∘F f)))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      ( (μ monad ∘F [ F ]₁ (id (S op) , id S , μ monad) ) ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g) ∘F f))) m
        ≡⟨ cong (λ X → (X ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g) ∘F f))) m) (AtkeyParameterizedMonad.assoc monad) ⟩
      ( (μ monad ∘F μ monad) ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g) ∘F f))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ monad ∘F (μ monad ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g) ∘F f)))) m
        ≡⟨ cong₂ (λ X Y → (μ monad ∘F (μ monad ∘F [ F ]₁ (X , Y , ([ F ]₁ (id (S op) , id S , g) ∘F f)))) m) (sym $ Category.left-id (S op)) (sym $ Category.left-id S) ⟩
      (μ monad ∘F (μ monad ∘F [ F ]₁ ((id (S op) ∘Sop id (S op)) , (id S ∘S id S) , ([ F ]₁ (id (S op) , id S , g) ∘F f)))) m
        ≡⟨ cong (λ X → (μ monad ∘F (μ monad ∘F X)) m) (Functor.compose F) ⟩
      (μ monad ∘F (μ monad ∘F ([ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g))) ∘F [ F ]₁ (id (S op) , id S , f)))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ monad ∘F ((μ monad ∘F [ F ]₁ (id (S op) , id S , ([ F ]₁ (id (S op) , id S , g))) ) ∘F [ F ]₁ (id (S op) , id S , f))) m
        ≡⟨ cong (λ X → (μ monad ∘F (X ∘F [ F ]₁ (id (S op) , id S , f))) m) (sym $ naturalμ monad) ⟩
      (μ monad ∘F (([ F ]₁ (id (S op) , id S , g) ∘F μ monad) ∘F [ F ]₁ (id (S op) , id S , f))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ monad ∘F ([ F ]₁ (id (S op) , id S , g) ∘F (μ monad ∘F [ F ]₁ (id (S op) , id S , f)))) m
        ≡⟨ refl ⟩
      (m >>= f) >>= g ∎
