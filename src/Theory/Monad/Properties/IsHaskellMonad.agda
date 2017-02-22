
module Theory.Monad.Properties.IsHaskellMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary.HeterogeneousEquality 
--  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
--open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Haskell
open import Haskell.Monad renaming ( Monad to HaskellMonad )
open import Haskell.Applicative renaming ( Applicative to HaskellApplicative )
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Category
open import Theory.Functor
open import Theory.Natural.Transformation renaming ( NaturalTransformation to NatTrans )
open import Theory.Monad hiding ( monad )
open import Theory.Examples.Category
open import Theory.Functor.Properties.IsHaskellFunctor

Monad→HaskellMonad : {M : Functor (setCategory {lzero}) (setCategory {lzero})}
                   → Monad M → HaskellMonad ([ M ]₀)
Monad→HaskellMonad {M} monad = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicative
  ; law-right-id = law-right-id
  ; law-left-id = law-left-id
  ; law-assoc = law-assoc
  ; law-monad-fmap = law-monad-fmap
  } where
    C = setCategory {lzero}
    
    η = NatTrans.η (Monad.η monad)
    μ = NatTrans.η (Monad.μ monad)
    
    fmap : {α β : Type} → (α → β) → [ M ]₀ α → [ M ]₀ β
    fmap = [ M ]₁
    
    join : {α : Type} → [ M ]₀ ([ M ]₀ α) → [ M ]₀ α
    join {α} mma = μ α mma
    
    _>>=_ : {α β : Type} → [ M ]₀ α → (α → [ M ]₀ β) → [ M ]₀ β
    _>>=_ ma f = join (fmap f ma)
    
    return : {α : Type} → α → [ M ]₀ α
    return {α} a = η α a
    
    _<*>_ : {α β : Type} → [ M ]₀ (α → β) → [ M ]₀ α → [ M ]₀ β
    _<*>_ mf ma = mf >>= (λ f → fmap f ma)
    
    law-left-id : {α β : Type} (a : α) (k : α → [ M ]₀ β)
           → return a >>= k ≡ k a
    law-left-id {α} {β} a k = begin 
      (μ β ∘F ([ M ]₁ k ∘F η α)) a 
        ≡⟨ cong (λ X → (μ β ∘F X) a) (NatTrans.natural (Monad.η monad)) ⟩ 
      (μ β ∘F (η ([ M ]₀ β) ∘F [ Id[ C ] ]₁ k)) a 
        ≡⟨ refl ⟩ -- associativity of ∘F
      ((μ β ∘F η ([ M ]₀ β)) ∘F [ Id[ C ] ]₁ k) a 
        ≡⟨ cong (λ X → (X ∘F [ Id[ C ] ]₁ k) a) (Monad.η-right-coher monad) ⟩
      ((NatTrans.η Id⟨ M ⟩ β) ∘F [ Id[ C ] ]₁ k) a 
        ≡⟨ refl ⟩
      k a ∎
    
    law-right-id : {α : Type} (m : [ M ]₀ α) 
           → m >>= return ≡ m
    law-right-id {α} m = begin
      (μ α ∘F [ M ]₁ (η α)) m 
        ≡⟨ cong (λ X → X m) (Monad.η-left-coher monad) ⟩
      m ∎
    
    law-assoc : {α β γ : Type} (m : [ M ]₀ α) (k : α → [ M ]₀ β) (h : β → [ M ]₀ γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    law-assoc {α} {β} {γ} m k h = begin
      (μ γ ∘F [ M ]₁ (λ x → (μ γ ∘F ([ M ]₁ h ∘F k)) x)) m 
        ≡⟨ cong (λ X → (μ γ ∘F X) m) (Functor.compose M) ⟩
      (μ γ ∘F ([ M ]₁ (μ γ) ∘F [ M ]₁ ([ M ]₁ h ∘F k))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      ((μ γ ∘F [ M ]₁ (μ γ)) ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m
        ≡⟨ cong (λ X → (X ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m) (Monad.μ-coher monad) ⟩
      ((μ γ ∘F μ ([ M ]₀ γ)) ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F (μ ([ M ]₀ γ) ∘F [ M ]₁ ([ M ]₁ h ∘F k))) m
        ≡⟨ cong (λ X → (μ γ ∘F (μ ([ M ]₀ γ) ∘F X)) m) (Functor.compose M) ⟩
      (μ γ ∘F (μ ([ M ]₀ γ) ∘F ([ [ M ]∘[ M ] ]₁ h ∘F [ M ]₁ k))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F ((μ ([ M ]₀ γ) ∘F [ [ M ]∘[ M ] ]₁ h) ∘F [ M ]₁ k)) m
        ≡⟨ cong (λ X → (μ γ ∘F (X ∘F [ M ]₁ k)) m) (sym $ NatTrans.natural $ Monad.μ monad) ⟩
      (μ γ ∘F (([ M ]₁ h ∘F μ β) ∘F [ M ]₁ k)) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F ([ M ]₁ h ∘F (μ β ∘F [ M ]₁ k))) m ∎

    law-monad-fmap : {α β : Type} (f : α → β) (x : [ M ]₀ α) 
                 → fmap f x ≡ x >>= (return ∘F f)
    law-monad-fmap {α} {β} f x = begin
      [ M ]₁ f x 
        ≡⟨ cong (λ X → (X ∘F [ M ]₁ f) x) (sym $ Monad.η-left-coher monad) ⟩
      ((μ β ∘F [ M ]₁ (η β)) ∘F [ M ]₁ f) x
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ β ∘F ([ M ]₁ (η β) ∘F [ M ]₁ f)) x
        ≡⟨ cong (λ X → (μ β ∘F X) x) (sym $ Functor.compose M) ⟩
      (μ β ∘F ([ M ]₁ (η β ∘F f))) x ∎
    
    applicative : HaskellApplicative ([ M ]₀)
    applicative = record
      { pure = return
      ; _<*>_ = _<*>_
      ; functor = Functor→HaskellFunctor M
      ; law-id = law-id
      ; law-composition = law-composition
      ; law-homomorphism = law-homomorphism
      ; law-interchange = law-interchange
      ; law-applicative-fmap = law-applicative-fmap
      } where
        law-id : {α : Type} (v : [ M ]₀ α)
              → return idF <*> v ≡ v
        law-id {α} v = begin
          return idF >>= (λ f → fmap f v)
            ≡⟨ law-left-id idF (λ f → fmap f v) ⟩
          fmap idF v
            ≡⟨ cong (λ X → X v) (Functor.id M) ⟩
          v ∎
        
        law-composition : {α β γ : Type} (u : [ M ]₀ (β → γ)) (v : [ M ]₀ (α → β)) (w : [ M ]₀ α) 
                       → ((return _∘′_ <*> u) <*> v) <*> w ≡ u <*> (v <*> w)
        law-composition {α} {β} {γ} u v w = begin
          ((return _∘′_ >>= (λ f → fmap f u)) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → (X >>= (λ g → fmap g v)) >>= (λ h → fmap h w) ) (law-left-id _∘′_ (λ f → fmap f u)) ⟩
          ((fmap _∘′_ u) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → (X >>= (λ g → fmap g v)) >>= (λ h → fmap h w)) (law-monad-fmap _∘′_ u) ⟩
          ((u >>= (return ∘F _∘′_)) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → X >>= (λ h → fmap h w)) (sym $ law-assoc u (return ∘F _∘′_) (λ g → fmap g v)) ⟩
          (u >>= (λ x → (return ∘F _∘F_) x >>= (λ g → fmap g v))) >>= (λ h → fmap h w) 
            ≡⟨ sym $ law-assoc u (λ x → ((return ∘F _∘F_) x >>= (λ g → fmap g v))) (λ h → fmap h w) ⟩
          u >>= (λ f → (return (_∘F_ f) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → X >>= (λ h → fmap h w)) (law-left-id (_∘F_ f) (λ g → fmap g v)))) ⟩
          u >>= (λ f → fmap (_∘F_ f) v >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → X >>= (λ h → fmap h w)) (law-monad-fmap (_∘F_ f) v))) ⟩
          u >>= (λ f → (v >>= (return ∘F (_∘F_ f))) >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → sym $ law-assoc v (return ∘F (_∘′_ f)) (λ h → fmap h w))) ⟩
          u >>= (λ f → v >>= (λ g → return (f ∘F g) >>= (λ h → fmap h w) ) )
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → law-left-id (f ∘F g) (λ h → fmap h w))))) ⟩
          u >>= (λ f → v >>= (λ g → fmap (f ∘F g) w))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → law-monad-fmap (f ∘F g) w)))) ⟩
          u >>= (λ f → v >>= (λ g → w >>= (return ∘F (f ∘F g))))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → cong (λ X → w >>= X) (fun-ext (λ x → sym $ law-left-id (g x) (return ∘F f))))))) ⟩
          u >>= (λ f → v >>= (λ g → w >>= (λ x → (return ∘F g) x >>= (return ∘F f))))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → law-assoc w (return ∘F g) (return ∘F f))))) ⟩
          u >>= (λ f → v >>= (λ g → (w >>= (return ∘F g)) >>= (return ∘F f)))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → cong (λ X → v >>= X) (fun-ext (λ g → cong (λ X → X >>= (return ∘F f)) (sym $ law-monad-fmap g w))))) ⟩
          u >>= (λ f → v >>= (λ g → fmap g w >>= (return ∘F f)))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → law-assoc v (λ g → fmap g w) (return ∘F f))) ⟩
          u >>= (λ f → (v >>= (λ g → fmap g w)) >>= (return ∘F f))
            ≡⟨ cong (λ X → u >>= X) (fun-ext (λ f → sym $ law-monad-fmap f (v >>= (λ g → fmap g w)))) ⟩
          u >>= (λ f → fmap f (v >>= (λ g → fmap g w))) ∎

        law-homomorphism : {α β : Type} (x : α) (f : α → β)
                        → return f <*> return x ≡ return (f x)
        law-homomorphism {α} {β} x f = begin
          return f >>= (λ f → fmap f (return x)) 
            ≡⟨ law-left-id f (λ f → fmap f (return x)) ⟩
          fmap f (return x) 
            ≡⟨ law-monad-fmap f (return x) ⟩
          return x >>= (return ∘F f)
            ≡⟨ law-left-id x (return ∘F f) ⟩
          return (f x) ∎
        
        law-interchange : {α β : Type} (u : [ M ]₀ (α → β)) (x : α) 
                       → u <*> return x ≡ return (λ f → f x) <*> u
        law-interchange {α} {β} u x = begin
          u >>= (λ f → fmap f (return x)) 
            ≡⟨ cong (λ X → u >>= X) (fun-ext $ λ f → law-monad-fmap f (return x)) ⟩
          u >>= (λ f → return x >>= (return ∘F f)) 
            ≡⟨ cong (λ X → u >>= X) (fun-ext $ λ f → law-left-id x (return ∘F f)) ⟩
          u >>= (λ f → return (f x))
            ≡⟨ refl ⟩
          u >>= (return ∘F (λ f → f x))
            ≡⟨ sym $ law-monad-fmap (λ z → z x) u ⟩
          fmap (λ f → f x) u
            ≡⟨ sym $ law-left-id (λ f → f x) (λ g → fmap g u) ⟩
          return (λ f → f x) >>= (λ g → fmap g u) ∎
        
        law-applicative-fmap : {α β : Type} (f : α → β) (x : [ M ]₀ α)
                           → fmap f x ≡ return f <*> x
        law-applicative-fmap {α} {β} f x = sym $ law-left-id f (λ g → fmap g x)

