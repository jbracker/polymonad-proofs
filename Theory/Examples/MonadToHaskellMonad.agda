
module Theory.Examples.MonadToHaskellMonad where

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
open import Utilities
open import Haskell
open import Monad renaming ( Monad to HaskellMonad )
open import Applicative renaming ( Applicative to HaskellApplicative )
open import Functor renaming ( Functor to HaskellFunctor )
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation renaming ( NaturalTransformation to NatTrans )
open import Theory.Monad
open import Theory.Examples.Category
open import Theory.Examples.FunctorToHaskellFunctor

Monad→HaskellMonad : {M : Functor (setCategory {lzero}) (setCategory {lzero})}
                   → Monad M → HaskellMonad ([ M ]₀)
Monad→HaskellMonad {M} monad = record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicative
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssoc
  ; lawMonadFmap = lawMonadFmap
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
    
    lawIdR : {α β : Type} (a : α) (k : α → [ M ]₀ β)
           → return a >>= k ≡ k a
    lawIdR {α} {β} a k = begin 
      (μ β ∘F ([ M ]₁ k ∘F η α)) a 
        ≡⟨ cong (λ X → (μ β ∘F X) a) (NatTrans.natural (Monad.η monad)) ⟩ 
      (μ β ∘F (η ([ M ]₀ β) ∘F [ Id[ C ] ]₁ k)) a 
        ≡⟨ refl ⟩ -- associativity of ∘F
      ((μ β ∘F η ([ M ]₀ β)) ∘F [ Id[ C ] ]₁ k) a 
        ≡⟨ cong (λ X → (X ∘F [ Id[ C ] ]₁ k) a) (Monad.ηCoherR monad) ⟩
      ((NatTrans.η Id⟨ M ⟩ β) ∘F [ Id[ C ] ]₁ k) a 
        ≡⟨ refl ⟩
      k a ∎
    
    lawIdL : {α : Type} (m : [ M ]₀ α) 
           → m >>= return ≡ m
    lawIdL {α} m = begin
      (μ α ∘F [ M ]₁ (η α)) m 
        ≡⟨ cong (λ X → X m) (Monad.ηCoherL monad) ⟩
      m ∎
    
    lawAssoc : {α β γ : Type} (m : [ M ]₀ α) (k : α → [ M ]₀ β) (h : β → [ M ]₀ γ) 
             → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    lawAssoc {α} {β} {γ} m k h = begin
      (μ γ ∘F [ M ]₁ (λ x → (μ γ ∘F ([ M ]₁ h ∘F k)) x)) m 
        ≡⟨ cong (λ X → (μ γ ∘F X) m) (Functor.dist M) ⟩
      (μ γ ∘F ([ M ]₁ (μ γ) ∘F [ M ]₁ ([ M ]₁ h ∘F k))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      ((μ γ ∘F [ M ]₁ (μ γ)) ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m
        ≡⟨ cong (λ X → (X ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m) (Monad.μCoher monad) ⟩
      ((μ γ ∘F μ ([ M ]₀ γ)) ∘F [ M ]₁ ([ M ]₁ h ∘F k)) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F (μ ([ M ]₀ γ) ∘F [ M ]₁ ([ M ]₁ h ∘F k))) m
        ≡⟨ cong (λ X → (μ γ ∘F (μ ([ M ]₀ γ) ∘F X)) m) (Functor.dist M) ⟩
      (μ γ ∘F (μ ([ M ]₀ γ) ∘F ([ [ M ]∘[ M ] ]₁ h ∘F [ M ]₁ k))) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F ((μ ([ M ]₀ γ) ∘F [ [ M ]∘[ M ] ]₁ h) ∘F [ M ]₁ k)) m
        ≡⟨ cong (λ X → (μ γ ∘F (X ∘F [ M ]₁ k)) m) (sym $ NatTrans.natural $ Monad.μ monad) ⟩
      (μ γ ∘F (([ M ]₁ h ∘F μ β) ∘F [ M ]₁ k)) m
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ γ ∘F ([ M ]₁ h ∘F (μ β ∘F [ M ]₁ k))) m ∎

    lawMonadFmap : {α β : Type} (f : α → β) (x : [ M ]₀ α) 
                 → fmap f x ≡ x >>= (return ∘F f)
    lawMonadFmap {α} {β} f x = begin
      [ M ]₁ f x 
        ≡⟨ cong (λ X → (X ∘F [ M ]₁ f) x) (sym $ Monad.ηCoherL monad) ⟩
      ((μ β ∘F [ M ]₁ (η β)) ∘F [ M ]₁ f) x
        ≡⟨ refl ⟩ -- associativity of ∘F
      (μ β ∘F ([ M ]₁ (η β) ∘F [ M ]₁ f)) x
        ≡⟨ cong (λ X → (μ β ∘F X) x) (sym $ Functor.dist M) ⟩
      (μ β ∘F ([ M ]₁ (η β ∘F f))) x ∎
    
    applicative : HaskellApplicative ([ M ]₀)
    applicative = record
      { pure = return
      ; _<*>_ = _<*>_
      ; functor = Functor→HaskellFunctor M
      ; lawId = lawId
      ; lawComposition = lawComposition
      ; lawHomomorphism = lawHomomorphism
      ; lawInterchange = lawInterchange
      ; lawApplicativeFmap = lawApplicativeFmap
      } where
        lawId : {α : Type} (v : [ M ]₀ α)
              → return idF <*> v ≡ v
        lawId {α} v = begin
          return idF >>= (λ f → fmap f v)
            ≡⟨ lawIdR idF (λ f → fmap f v) ⟩
          fmap idF v
            ≡⟨ cong (λ X → X v) (Functor.id M) ⟩
          v ∎
        
        lawComposition : {α β γ : Type} (u : [ M ]₀ (β → γ)) (v : [ M ]₀ (α → β)) (w : [ M ]₀ α) 
                       → ((return _∘′_ <*> u) <*> v) <*> w ≡ u <*> (v <*> w)
        lawComposition {α} {β} {γ} u v w = begin
          ((return _∘′_ >>= (λ f → fmap f u)) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → (X >>= (λ g → fmap g v)) >>= (λ h → fmap h w) ) (lawIdR _∘′_ (λ f → fmap f u)) ⟩
          ((fmap _∘′_ u) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → (X >>= (λ g → fmap g v)) >>= (λ h → fmap h w)) (lawMonadFmap _∘′_ u) ⟩
          ((u >>= (return ∘F _∘′_)) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) 
            ≡⟨ cong (λ X → X >>= (λ h → fmap h w)) (sym $ lawAssoc u (return ∘F _∘′_) (λ g → fmap g v)) ⟩
          (u >>= (λ x → (return ∘F _∘F_) x >>= (λ g → fmap g v))) >>= (λ h → fmap h w) 
            ≡⟨ sym $ lawAssoc u (λ x → ((return ∘F _∘F_) x >>= (λ g → fmap g v))) (λ h → fmap h w) ⟩
          u >>= (λ f → (return (_∘F_ f) >>= (λ g → fmap g v)) >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → X >>= (λ h → fmap h w)) (lawIdR (_∘F_ f) (λ g → fmap g v)))) ⟩
          u >>= (λ f → fmap (_∘F_ f) v >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → X >>= (λ h → fmap h w)) (lawMonadFmap (_∘F_ f) v))) ⟩
          u >>= (λ f → (v >>= (return ∘F (_∘F_ f))) >>= (λ h → fmap h w) )
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → sym $ lawAssoc v (return ∘F (_∘′_ f)) (λ h → fmap h w))) ⟩
          u >>= (λ f → v >>= (λ g → return (f ∘F g) >>= (λ h → fmap h w) ) )
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → lawIdR (f ∘F g) (λ h → fmap h w))))) ⟩
          u >>= (λ f → v >>= (λ g → fmap (f ∘F g) w))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → lawMonadFmap (f ∘F g) w)))) ⟩
          u >>= (λ f → v >>= (λ g → w >>= (return ∘F (f ∘F g))))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → cong (λ X → w >>= X) (funExt (λ x → sym $ lawIdR (g x) (return ∘F f))))))) ⟩
          u >>= (λ f → v >>= (λ g → w >>= (λ x → (return ∘F g) x >>= (return ∘F f))))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → lawAssoc w (return ∘F g) (return ∘F f))))) ⟩
          u >>= (λ f → v >>= (λ g → (w >>= (return ∘F g)) >>= (return ∘F f)))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → cong (λ X → v >>= X) (funExt (λ g → cong (λ X → X >>= (return ∘F f)) (sym $ lawMonadFmap g w))))) ⟩
          u >>= (λ f → v >>= (λ g → fmap g w >>= (return ∘F f)))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → lawAssoc v (λ g → fmap g w) (return ∘F f))) ⟩
          u >>= (λ f → (v >>= (λ g → fmap g w)) >>= (return ∘F f))
            ≡⟨ cong (λ X → u >>= X) (funExt (λ f → sym $ lawMonadFmap f (v >>= (λ g → fmap g w)))) ⟩
          u >>= (λ f → fmap f (v >>= (λ g → fmap g w))) ∎

        lawHomomorphism : {α β : Type} (x : α) (f : α → β)
                        → return f <*> return x ≡ return (f x)
        lawHomomorphism {α} {β} x f = begin
          return f >>= (λ f → fmap f (return x)) 
            ≡⟨ lawIdR f (λ f → fmap f (return x)) ⟩
          fmap f (return x) 
            ≡⟨ lawMonadFmap f (return x) ⟩
          return x >>= (return ∘F f)
            ≡⟨ lawIdR x (return ∘F f) ⟩
          return (f x) ∎
        
        lawInterchange : {α β : Type} (u : [ M ]₀ (α → β)) (x : α) 
                       → u <*> return x ≡ return (λ f → f x) <*> u
        lawInterchange {α} {β} u x = begin
          u >>= (λ f → fmap f (return x)) 
            ≡⟨ cong (λ X → u >>= X) (funExt $ λ f → lawMonadFmap f (return x)) ⟩
          u >>= (λ f → return x >>= (return ∘F f)) 
            ≡⟨ cong (λ X → u >>= X) (funExt $ λ f → lawIdR x (return ∘F f)) ⟩
          u >>= (λ f → return (f x))
            ≡⟨ refl ⟩
          u >>= (return ∘F (λ f → f x))
            ≡⟨ sym $ lawMonadFmap (λ z → z x) u ⟩
          fmap (λ f → f x) u
            ≡⟨ sym $ lawIdR (λ f → f x) (λ g → fmap g u) ⟩
          return (λ f → f x) >>= (λ g → fmap g u) ∎
        
        lawApplicativeFmap : {α β : Type} (f : α → β) (x : [ M ]₀ α)
                           → fmap f x ≡ return f <*> x
        lawApplicativeFmap {α} {β} f x = sym $ lawIdR f (λ g → fmap g x)

