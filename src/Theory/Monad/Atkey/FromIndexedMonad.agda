
module Theory.Monad.Atkey.FromIndexedMonad where

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
open import Extensionality
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
open import Theory.Monad.Atkey.ToIndexedMonad
open import Theory.Category.Examples
open import Theory.TwoCategory.Examples

open StrictTwoCategory
open Category 
open Triple

IxTyCon→AtkeyFunctor
  : {ℓS₀ ℓS₁ : Level}
  → {S : Category {ℓS₀} {ℓS₁}}
  → (Functor (S op ×C S) (S op ×C S))
  → (Obj (S op) → Obj S → TyCon)
  → (Functor (S op ×C S ×C setCategory {lzero}) (setCategory {lzero}))
IxTyCon→AtkeyFunctor {S = S} SF F = functor F₀ F₁ {!!} {!!}
  where
    F₀ : Obj ((S op) ×C S ×C setCategory) → Obj setCategory
    F₀ (s₀ , s₁ , a) = F s₀ s₁ a
    
    F₁ : {a b : Obj ((S op) ×C S ×C setCategory)} → Hom ((S op) ×C S ×C setCategory) a b → Hom setCategory (F₀ a) (F₀ b)
    F₁ {sa₀ , sa₁ , a} {sb₀ , sb₁ , b} {sf₀ , sf₁ , f} = {!!}

IxMonad→AtkeyParameterizedMonad
  : {ℓS₀ ℓS₁ : Level}
  → (S : Category {ℓS₀} {ℓS₁})
  → (F : Functor (S op ×C S ×C setCategory {lzero}) (setCategory {lzero}))
  → (monad : IxMonad (Obj S) (AtkeyFunctor→IxTyCon F))
  → ({α β : Type} {i j : Obj S} → (f : α → β) → (ma : (AtkeyFunctor→IxTyCon F) i j α) → IxMonad.bind monad ma (IxMonad.return monad ∘F f) ≡ [ F ]₁ (id (S op) {i} , id S {j} , f) ma)
  → AtkeyParameterizedMonad setCategory S F
IxMonad→AtkeyParameterizedMonad S F monad fmap-rel  = record
  { η = return
  ; μ = join
  ; naturalη = {!!}
  ; dinaturalη = {!!}
  ; naturalμ = {!!}
  ; naturalμ₁ = {!!}
  ; naturalμ₂ = {!!}
  ; dinaturalμ = {!!}
  ; assoc = {!!}
  ; left-id = λ {x} {s₁} {s₂} → left-id' {x} {s₁} {s₂}
  ; right-id = λ {x} {s₁} {s₂} → right-id' {x} {s₁} {s₂}
  } where
    open IxMonad monad hiding ( bind )
    
    left-id' : {A : Obj setCategory} {s₁ s₂ : Obj S} 
             → join ∘F [ F ]₁ (id (S op) , id S , return) ≡ (λ x → x)
    left-id' = fun-ext $ λ x → begin
      ([ F ]₁ (id (S op) , id S , return) x) >>= (λ x → x)
        ≡⟨ cong (λ X → _>>=_ X (λ x₁ → x₁)) (sym (fmap-rel return x)) ⟩
      (x >>= (return ∘F return)) >>= (λ x → x)
        ≡⟨ sym (law-assoc x (return ∘F return) (λ y → y)) ⟩
      x >>= (λ y → return (return y) >>= (λ y → y))
        ≡⟨ cong (λ X → _>>=_ x X) (fun-ext (λ y → law-right-id (return y) (λ y → y))) ⟩
      x >>= return
        ≡⟨ law-left-id x ⟩
      x ∎
    
    right-id' : {x : Obj setCategory} {s₁ s₂ : Obj S} → join ∘F return ≡ id setCategory
    right-id' = fun-ext $ λ x → law-right-id x (λ y → y)
    
{-
law-left-id : ∀ {α : Type} {i j : Ixs}
           → (m : M i j α)
           → m >>= return ≡ m
-}

{-record
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
-}
