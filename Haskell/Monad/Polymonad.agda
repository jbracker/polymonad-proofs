 
module Monad.Polymonad where

-- Stdlib
open import Function hiding ( id ; _∘_ ) renaming ( _∘′_ to _∘_ )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad
open import Applicative
open import Monad
open import Identity

data MonadTyCons : Set where
  MonadTC : MonadTyCons

data MonadBinds : (M N P : IdTyCons ⊎ MonadTyCons) → Set where
  MonadB   : MonadBinds (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)
  FunctorB : MonadBinds (inj₂ MonadTC) idTC (inj₂ MonadTC)
  ApplyB   : MonadBinds idTC (inj₂ MonadTC) (inj₂ MonadTC)
  ReturnB  : MonadBinds idTC idTC (inj₂ MonadTC)

bindMonad : ∀ {M : TyCon} → (m : Monad M)
          → [ M , M ]▷ M
bindMonad m = mBind m

bindFunctor : ∀ {M : TyCon} → (m : Monad M)
            → [ M , Identity ]▷ M
bindFunctor m ma f = mBind m ma (λ a → mReturn m (f a))

bindApply : ∀ {M : TyCon} → (m : Monad M)
          → [ Identity , M ]▷ M
bindApply m ma f = mBind m (mReturn m ma) f

bindReturn : ∀ {M : TyCon} → (m : Monad M)
           → [ Identity , Identity ]▷ M
bindReturn m ma f = mReturn m (f ma)

Monad→Polymonad : ∀ {M : TyCon} 
                → (monad : Monad M)
                → Polymonad (IdTyCons ⊎ MonadTyCons) idTC
Monad→Polymonad {M = M'} monad = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; lawId = lawId
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1 
  ; lawDiamond2 = lawDiamond2
  ; lawAssoc = lawAssoc
  ; lawClosure = lawClosure
  } where
    TyCons = IdTyCons ⊎ MonadTyCons
    
    Id = idTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ MonadTC) = M'
    
    B[_,_]▷_ : TyCons → TyCons → TyCons → Set
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ m            , n            ]▷ inj₁ IdentTC = ⊥
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ MonadTC = MonadBinds idTC idTC (inj₂ MonadTC)
    B[ inj₁ IdentTC , inj₂ MonadTC ]▷ inj₂ MonadTC = MonadBinds idTC (inj₂ MonadTC) (inj₂ MonadTC)
    B[ inj₂ MonadTC , inj₁ IdentTC ]▷ inj₂ MonadTC = MonadBinds (inj₂ MonadTC) idTC (inj₂ MonadTC)
    B[ inj₂ MonadTC , inj₂ MonadTC ]▷ inj₂ MonadTC = MonadBinds (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC)
  
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) ()
    bind (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) ()
    bind (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) ()
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) ReturnB  = bindReturn monad
    bind (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) ApplyB   = bindApply monad
    bind (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) FunctorB = bindFunctor monad
    bind (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) MonadB   = bindMonad monad

    lawId : ⟨ Id ⟩ ≡ Identity
    lawId = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ MonadTC) = FunctorB

    lawFunctor2 :  ∀ (M : TyCons) → (b : B[ M , Id ]▷ M)
                → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id lawId) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB   m = refl
    lawFunctor2 (inj₂ MonadTC) FunctorB m = Monad.lawIdL monad m
    
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ MonadTC) ReturnB = ReturnB
    lawMorph1 (inj₂ MonadTC) (inj₁ IdentTC) ()
    lawMorph1 (inj₂ MonadTC) (inj₂ MonadTC) FunctorB = ApplyB

    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ MonadTC) ReturnB = ReturnB
    lawMorph2 (inj₂ MonadTC) (inj₁ IdentTC) ()
    lawMorph2 (inj₂ MonadTC) (inj₂ MonadTC) ApplyB = FunctorB
    
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id lawId) ≡ (bind Id M N b₂) (id lawId v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ MonadTC) ReturnB ReturnB v f = refl
    lawMorph3 (inj₂ MonadTC) (inj₁ IdentTC) () b₂ v f
    lawMorph3 (inj₂ MonadTC) (inj₂ MonadTC) FunctorB ApplyB v f = begin
      bindFunctor monad (f v) (id lawId) 
        ≡⟨ refl ⟩
      mBind monad (f v) (λ a → mReturn monad (id lawId a))
        ≡⟨ refl ⟩
      mBind monad (f v) (mReturn monad)
        ≡⟨ mLawIdL monad (f v) ⟩
      f v
        ≡⟨ sym (mLawIdR monad (id lawId v) f) ⟩
      mBind monad (mReturn monad (id lawId v)) f
        ≡⟨ refl ⟩
      bindApply monad (id lawId v) f ∎
    
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC , IdentB , ApplyB ) = inj₂ MonadTC , ApplyB  , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ MonadTC , ReturnB , ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , ReturnB , MonadB  ) = inj₂ MonadTC , ApplyB  , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ MonadTC) R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ MonadTC) R (inj₁ IdentTC) (inj₂ MonadTC , ApplyB , ())
    lawDiamond1 (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , ApplyB , FunctorB) = inj₂ MonadTC , FunctorB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , ApplyB , MonadB  ) = inj₂ MonadTC , MonadB   , ApplyB
    lawDiamond1 (inj₂ MonadTC) N R T (inj₁ IdentTC , () , b₂)
    lawDiamond1 (inj₂ MonadTC) N R (inj₁ IdentTC) (inj₂ MonadTC , b₁ , ())
    lawDiamond1 (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , FunctorB , FunctorB) = inj₁ IdentTC , IdentB  , FunctorB
    lawDiamond1 (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , FunctorB , MonadB  ) = inj₂ MonadTC , ApplyB   , MonadB
    lawDiamond1 (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , MonadB   , FunctorB) = inj₂ MonadTC , FunctorB , MonadB
    lawDiamond1 (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , MonadB   , MonadB  ) = inj₂ MonadTC , MonadB   , MonadB
    
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ MonadTC , FunctorB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC , ReturnB , ())
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC , ReturnB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , ReturnB , MonadB) = inj₂ MonadTC , FunctorB , FunctorB
    lawDiamond2 M (inj₁ IdentTC) (inj₂ MonadTC) T (inj₁ IdentTC , () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC , ApplyB , ())
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC , ApplyB , ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
    lawDiamond2 (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , ApplyB , MonadB) = inj₂ MonadTC , FunctorB , MonadB
    lawDiamond2 M (inj₂ MonadTC) R T (inj₁ IdentTC , () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₂ MonadTC) R (inj₁ IdentTC) (inj₂ MonadTC , b₁ , ())
    lawDiamond2 (inj₂ MonadTC) (inj₂ MonadTC) R (inj₁ IdentTC) (inj₂ MonadTC , b₁ , ())
    lawDiamond2 (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , FunctorB , ApplyB) = inj₂ MonadTC , ApplyB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , MonadB   , ApplyB) = inj₂ MonadTC , ApplyB , MonadB
    lawDiamond2 (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC , FunctorB , MonadB) = inj₂ MonadTC , MonadB , FunctorB
    lawDiamond2 (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC , MonadB   , MonadB) = inj₂ MonadTC , MonadB , MonadB

    lawIdRF : ∀ {M : TyCon} 
            → (monad : Monad M) 
            → ∀ {α β γ : Type} 
            → (f : α → β) → (k : β → M γ) 
            → (λ x → mBind monad (mReturn monad (f x)) k) ≡ (λ x → k (f x))
    lawIdRF monad f k = funExt (λ x → mLawIdR monad (f x) k)
    
    lawAssoc : ∀ (M N P R T S : TyCons) 
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB () () IdentB m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) R (inj₁ IdentTC) (inj₂ MonadTC) IdentB b₂ b₃ () m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) IdentB ApplyB () ReturnB m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) IdentB ReturnB ReturnB ApplyB m f g = begin
      bindReturn monad (bindId m f) g 
        ≡⟨ refl ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (mLawIdR monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) IdentB ApplyB ApplyB ApplyB m f g = begin
      bindApply monad (bindId m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (mLawIdR monad m (λ x → mBind monad (mReturn monad (f x)) g)) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc (inj₂ MonadTC) N (inj₁ IdentTC) R T S () b₂ b₃ b₄ m f g
    lawAssoc M N (inj₂ MonadTC) R (inj₁ IdentTC) S b₁ () b₃ b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g = begin
      bindFunctor monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn  monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ mLawIdR monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ refl ⟩
      bindReturn monad m (λ x → bindId (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) FunctorB FunctorB IdentB FunctorB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ a → mBind monad (mReturn monad (f a)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (lawIdRF monad f (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ a → mReturn monad (g (f a)))
        ≡⟨ refl ⟩
      bindFunctor monad m (λ x → bindId (f x) g) ∎
    lawAssoc M (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc M (inj₂ MonadTC) (inj₂ MonadTC) R (inj₂ MonadTC) (inj₁ IdentTC) b₁ b₂ () b₄ m f g
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) ReturnB FunctorB ReturnB ApplyB m f g = begin
      bindFunctor monad (bindReturn monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ mLawIdR monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (mLawIdR monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) ApplyB FunctorB FunctorB ApplyB m f g = begin
      bindFunctor monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) (λ a → mReturn monad (g a)) 
        ≡⟨ cong (λ x → mBind monad x (λ a → mReturn monad (g a)) ) (mLawIdR monad m f) ⟩
      mBind monad (f m) (λ a → mReturn monad (g a))
        ≡⟨ sym (mLawIdR monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindFunctor monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) ReturnB MonadB ApplyB ApplyB m f g = begin
      bindMonad monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (mLawIdR monad m ((λ x → mBind monad (mReturn monad (f x)) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) ApplyB MonadB MonadB ApplyB m f g = begin
      bindMonad monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) g 
        ≡⟨ cong (λ x → mBind monad x g) (mLawIdR monad m f) ⟩
      mBind monad (f m) g
        ≡⟨ sym (mLawIdR monad m ((λ x → mBind monad (f x) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindMonad monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) FunctorB FunctorB ReturnB MonadB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (funExt (λ x → mLawIdR monad (f x) ((λ a → mReturn monad (g a))))) ⟩
      mBind monad m (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindReturn monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) MonadB FunctorB FunctorB MonadB m f g = begin
      bindFunctor monad (bindMonad monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m f) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m f ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindFunctor monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) FunctorB MonadB ApplyB MonadB m f g = begin
      bindMonad monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) g 
        ≡⟨ sym (mLawAssoc monad m ((λ a → mReturn monad (f a))) g) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindApply monad (f x) g) ∎
    lawAssoc (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) MonadB MonadB MonadB MonadB m f g = begin
      bindMonad monad (bindMonad monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m f) g
        ≡⟨ sym (mLawAssoc monad m f g) ⟩
      mBind monad m (λ x → mBind monad (f x) g)
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindMonad monad (f x) g) ∎

    lawClosure : ∀ (M N P S T U : TyCons)
               → ( B[ M , N ]▷ P × B[ S , Id ]▷ M × B[ T , Id ]▷ N × B[ P , Id ]▷ U )
               → B[ S , T ]▷ U
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB ) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (IdentB , IdentB , IdentB , ReturnB ) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (ReturnB , IdentB , IdentB , ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) P (inj₁ IdentTC) (inj₂ MonadTC) U (b₁ , IdentB , () , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) T U (() , IdentB , b₃ , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) T (inj₁ IdentTC) (ApplyB , IdentB , b₃ , ())
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (ApplyB , IdentB , ReturnB  , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₁ IdentTC) N P (inj₂ MonadTC) T U (b₁ , () , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) S (inj₁ IdentTC) U (() , b₂ , IdentB , b₄)
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) S (inj₁ IdentTC) (inj₁ IdentTC) (FunctorB , b₂ , IdentB , ())
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (FunctorB , ReturnB  , IdentB , FunctorB) = ReturnB
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
    lawClosure (inj₂ MonadTC) (inj₁ IdentTC) P S (inj₂ MonadTC) U (b₁ , b₂ , () , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) S T (inj₁ IdentTC) (() , b₂ , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) S T (inj₁ IdentTC) (b₁ , b₂ , b₃ , ())
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) S T (inj₂ MonadTC) (() , b₂ , b₃ , b₄)
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ MonadTC) (MonadB , ReturnB  , ReturnB  , FunctorB) = ReturnB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (MonadB , FunctorB , ReturnB  , FunctorB) = FunctorB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₁ IdentTC) (inj₂ MonadTC) (inj₂ MonadTC) (MonadB , ReturnB  , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (inj₂ MonadTC) (MonadB , FunctorB , FunctorB , FunctorB) = MonadB

open Polymonad.Polymonad

Polymonad→Monad : ∀ {TyCons : Set} {Id : TyCons}
                → (pm : Polymonad TyCons Id)
                → (∃ λ(M : TyCons) → B[ M , M ] pm ▷ M × B[ Id , Id ] pm ▷ M)
                → (∃ λ(M : TyCons) → Monad ⟨ pm ▷ M ⟩)
Polymonad→Monad {TyCons = TyCons} {Id = Id} pm (mTC , bindB , returnB) = mTC , (record
  { _>>=_ = _>>=_
  ; return = return
  ; applicative = applicativeFromMonad _>>=_ return lawIdL lawIdR lawAssocM
  ; lawIdR = lawIdR
  ; lawIdL = lawIdL
  ; lawAssoc = lawAssocM
  ; lawMonadFmap = λ f x → refl
  }) where
    M = ⟨ pm ▷ mTC ⟩
    
    _>>=_ = bind pm bindB
    
    returnBind = bind pm returnB
    
    return : ∀ {α} → α → M α
    return x = returnBind (id (lawId pm) x) (id (lawId pm))
    
    functorB = lawFunctor1 pm mTC
    functor = bind pm functorB
    functorLaw = lawFunctor2 pm mTC functorB
    
    applyB = lawMorph1 pm mTC mTC functorB
    apply = bind pm applyB
    
    lawIdR : ∀ {α β : Type} 
           → (a : α) → (k : α → M β) 
           → return a >>= k ≡ k a
    lawIdR a k = let x = id (lawId pm) a; id' = id (lawId pm) in begin
      return a >>= k 
        ≡⟨ refl ⟩ -- Def
      returnBind x id' >>= k
        ≡⟨ lawAssoc pm Id Id mTC mTC mTC mTC returnB bindB applyB applyB x id' k ⟩ -- Assoc
      apply x (λ y → apply (id' y) k)
        ≡⟨ cong (λ X → apply x X) (funExt (λ y → sym (lawMorph3 pm mTC mTC functorB applyB y k))) ⟩ -- Paired
      apply x (λ y → functor (k y) (id (lawId pm)))
        ≡⟨ sym (lawMorph3 pm mTC mTC functorB applyB a ((λ y → functor (k y) (id (lawId pm))))) ⟩ -- Paired
      functor ((λ y → functor (k y) (id (lawId pm))) a) (id (lawId pm))
        ≡⟨ refl ⟩ -- Eval
      functor (functor (k a) (id (lawId pm))) (id (lawId pm))
        ≡⟨ cong (λ X → functor X (id (lawId pm))) (functorLaw (k a)) ⟩ -- Functor
      functor (k a) (id (lawId pm))
        ≡⟨ functorLaw (k a) ⟩ -- Functor
      k a ∎

    lawIdL : ∀ {α : Type} 
           → (m : M α)
           → m >>= return ≡ m
    lawIdL m = begin
      m >>= return 
        ≡⟨ refl ⟩ -- Def
      m >>= (λ y → returnBind (id (lawId pm) y) (id (lawId pm)))
        ≡⟨ sym (lawAssoc pm mTC Id mTC Id mTC mTC functorB functorB returnB bindB m (id (lawId pm)) (id (lawId pm))) ⟩ -- Assoc
      functor (functor m (id (lawId pm))) (id (lawId pm))
        ≡⟨ cong (λ X → functor X (id (lawId pm))) (functorLaw m) ⟩ -- Functor
      functor m (id (lawId pm))
        ≡⟨ functorLaw m ⟩ -- Functor
      m ∎
    
    lawAssocM : ∀ {α β γ : Type} 
              → (m : M α) → (k : α → M β) → (h : β → M γ) 
              → m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h
    lawAssocM m k h = begin
      m >>= (λ x → k x >>= h) 
        ≡⟨ sym (lawAssoc pm mTC mTC mTC mTC mTC mTC bindB bindB bindB bindB m k h) ⟩ -- Assoc
      (m >>= k) >>= h ∎
    
