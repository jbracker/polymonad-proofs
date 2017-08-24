
module Theory.Monad.Atkey.Properties.ToIndexedMonad where

-- Stdlib
open import Level
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
open import Haskell.Functor renaming ( Functor to HaskFunctor )
open import Haskell.Parameterized.Indexed.Monad
open import Theory.Triple
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.Monad.Definition hiding ( monad )
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.Definition
open import Theory.Monad.Atkey
open import Theory.Category.Examples.SetCat
open import Theory.TwoCategory.Examples.Functor

open StrictTwoCategory
open Category

AtkeyFunctor→IxTyCon
  : {ℓS₀ ℓS₁ : Level}
  → {S : Category {ℓS₀} {ℓS₁}}
  → AtkeyParameterizedMonad (Hask {zero}) S
  → (Obj S → Obj S → TyCon)
AtkeyFunctor→IxTyCon F s₁ s₂ A = [ AtkeyParameterizedMonad.T F ]₀ (s₁ , s₂ , A)

AtkeyParameterizedMonad→IxMonad
  : {ℓS₀ ℓS₁ : Level}
  → (S : Category {ℓS₀} {ℓS₁})
  → (monad : AtkeyParameterizedMonad (Hask {zero}) S)
  → IxMonad (Obj S) (AtkeyFunctor→IxTyCon monad)
AtkeyParameterizedMonad→IxMonad S monad = record
  { _>>=_ = _>>=_
  ; return = return
  ; functor = λ i j → record 
    { fmap = fmap 
    ; law-id = law-fmap-id i j 
    ; law-compose = law-fmap-compose i j
    }
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  } where
    SetCat = setCategory {zero}
    F = AtkeyParameterizedMonad.T monad
    M = AtkeyFunctor→IxTyCon monad
    Ixs = Obj S
    
    _∘S_ = Category._∘_ S
    _∘Sop_ = Category._∘_ (S op)

    fmap : {α β : Type} {i j : Ixs}
         → (α → β) → M i j α → M i j β
    fmap {i = i} {j} f ma = [ F ]₁ (id (S op) {i} , id S {j} , f) ma
    
    join : {α : Type} {i j k : Ixs} 
         → M i j (M j k α) → M i k α
    join mma = AtkeyParameterizedMonad.μ monad mma
    
    _>>=_ : {α β : Type} {i j k : Ixs} 
          → M i j α → (α → M j k β) → M i k β
    _>>=_ ma fm = join $ fmap fm ma
    
    return : {α : Type} {i : Ixs} 
           → α → M i i α
    return a = AtkeyParameterizedMonad.η monad a
    
    open AtkeyParameterizedMonad
    
    abstract
      law-fmap-id : (i j : Ixs) → {α : Type} → fmap {α} {α} {i} {j} (λ x → x) ≡ (λ x → x)
      law-fmap-id i j {α} = Functor.id F

    abstract
      law-fmap-compose : (i j : Ixs) → {α β γ : Type} 
                       → (f : β → γ) → (g : α → β)
                       → fmap {α} {γ} {i} {j} (f ∘F g) ≡ fmap f ∘F fmap g
      law-fmap-compose i j {α} {β} {γ} f g = begin
        [ F ]₁ (id (S op) {i} , id S {j} , (f ∘F g))
          ≡⟨ cong₂ (λ X Y → [ F ]₁ (X , Y , (f ∘F g))) (sym (Category.left-id S)) (sym (Category.left-id S)) ⟩
        [ F ]₁ ((id (S op) {i} ∘Sop id (S op) {i}) , (id S {j} ∘S id S {j}) , (f ∘F g))
          ≡⟨ Functor.compose F ⟩
        [ F ]₁ (id (S op) {i} , id S {j} , f) ∘F [ F ]₁ (id (S op) {i} , id S {j} , g) ∎
      
    abstract
      law-monad-fmap : {α β : Type} {i j : Ixs} 
                     → (f : α → β)
                     → (ma : M i j α) 
                     → ma >>= (return ∘F f) ≡ fmap {α} {β} {i} {j} f ma
      law-monad-fmap {α} {β} {i} {j} f ma = begin
        (μ monad ∘F [ F ]₁ (id (S op) {i} , id S {j} , (η monad ∘F f))) ma 
          ≡⟨ cong₂ (λ X Y → (μ monad ∘F [ F ]₁ (X , Y , (η monad ∘F f))) ma) (sym (Category.left-id (S op))) (sym (Category.left-id S)) ⟩
        (μ monad ∘F [ F ]₁ ((id (S op) {i} ∘Sop id (S op) {i}) , (id S {j} ∘S id S {j}) , (η monad ∘F f))) ma 
          ≡⟨ cong (λ X → (μ monad ∘F X) ma) (Functor.compose F) ⟩
        (μ monad ∘F ([ F ]₁ (id (S op) {i} , id S {j} , η monad) ∘F [ F ]₁ (id (S op) {i} , id S {j} , f))) ma 
          ≡⟨ refl ⟩
        ((μ monad ∘F [ F ]₁ (id (S op) {i} , id S {j} , η monad)) ∘F [ F ]₁ (id (S op) {i} , id S {j} , f)) ma 
          ≡⟨ cong (λ X → (X ∘F [ F ]₁ (id (S op) {i} , id S {j} , f)) ma ) (AtkeyParameterizedMonad.left-id monad) ⟩
        ((λ x → x) ∘F [ F ]₁ (id (S op) {i} , id S {j} , f)) ma 
          ≡⟨ refl ⟩
        [ F ]₁ (id (S op) {i} , id S {j} , f) ma ∎
    
    abstract
      law-right-id : {α β : Type} {i j : Ixs} 
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
    
    abstract
      law-left-id : {α : Type} {i j : Ixs}
                  → (m : M i j α) 
                  → m >>= return ≡ m
      law-left-id {α} {i} {j} m = begin
        m >>= return 
          ≡⟨ refl ⟩
        (μ monad ∘F [ F ]₁ (id (S op) {i} , id S {j} , η monad)) m
          ≡⟨ cong (λ X →  X m) (AtkeyParameterizedMonad.left-id monad) ⟩
        m ∎
    
    abstract
      law-assoc : {α β γ : Type} {i j k l : Ixs}
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

