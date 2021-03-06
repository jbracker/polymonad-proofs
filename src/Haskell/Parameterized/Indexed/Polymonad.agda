 
module Haskell.Parameterized.Indexed.Polymonad where

-- Stdlib
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Extensionality
open import Haskell
open import Identity
open import Polymonad.Definition
open import Haskell.Parameterized.Indexed.Monad

open IxMonad renaming (bind to mBind; return to mReturn; law-assoc to mLawAssoc)

IxMonad→Polymonad : ∀ {n} {Ixs : Set n} {M : Ixs → Ixs → TyCon} 
                  → (monad : IxMonad Ixs M)
                  → Polymonad (IdTyCons ⊎ IxMonadTyCons Ixs) idTC
IxMonad→Polymonad {n = n} {Ixs = Ixs} {M = M'} monad = record 
  { B[_,_]▷_ = B[_,_]▷_
  ; ⟨_⟩ = ⟨_⟩
  ; bind = λ {m} {n} {p} b → bind m n p b
  ; law-id = law-id
  ; lawFunctor1 = lawFunctor1
  ; lawFunctor2 = lawFunctor2
  ; lawMorph1 = lawMorph1 
  ; lawMorph2 = lawMorph2
  ; lawMorph3 = lawMorph3
  ; lawDiamond1 = lawDiamond1 
  ; lawDiamond2 = lawDiamond2
  ; law-assoc = law-assoc
  ; lawClosure = lawClosure
  } where
    TyCons = IdTyCons ⊎ IxMonadTyCons Ixs
    
    Id = idTC
    
    ⟨_⟩ : TyCons → TyCon
    ⟨_⟩ (inj₁ IdentTC) = Identity
    ⟨_⟩ (inj₂ (IxMonadTC i j)) = M' i j
    
    B[_,_]▷_ : TyCons → TyCons → TyCons → Set n
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₁ IdentTC = IdBinds
    B[ m            , n            ]▷ inj₁ IdentTC = Lift ⊥
    B[ inj₁ IdentTC , inj₁ IdentTC ]▷ inj₂ (IxMonadTC i j) = IxMonadBinds Ixs idTC idTC (inj₂ (IxMonadTC i j))
    B[ inj₁ IdentTC , inj₂ (IxMonadTC i j) ]▷ inj₂ (IxMonadTC k l) = IxMonadBinds Ixs idTC (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l))
    B[ inj₂ (IxMonadTC i j) , inj₁ IdentTC ]▷ inj₂ (IxMonadTC k l) = IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) idTC (inj₂ (IxMonadTC k l))
    B[ inj₂ (IxMonadTC i j) , inj₂ (IxMonadTC k l) ]▷ inj₂ (IxMonadTC n m) = IxMonadBinds Ixs (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC n m))
    
    bind : (M N P : TyCons) → B[ M , N ]▷ P → [ ⟨ M ⟩ , ⟨ N ⟩ ]▷ ⟨ P ⟩
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB = bindId
    bind (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC m .m)) ReturnB = bindReturn monad
    bind (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (lift ())
    bind (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC .k .l)) ApplyB = bindApply monad
    bind (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (lift ())
    bind (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) FunctorB = bindFunctor monad
    bind (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (lift ())
    bind (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .i .l)) MonadB = bindMonad monad
    
    law-id : ⟨ Id ⟩ ≡ Identity
    law-id = refl
    
    lawFunctor1 : ∀ (M : TyCons) → B[ M , Id ]▷ M
    lawFunctor1 (inj₁ IdentTC) = IdentB
    lawFunctor1 (inj₂ (IxMonadTC i j)) = FunctorB
    
    lawFunctor2 : ∀ (M : TyCons) → (b : B[ M , Id ]▷ M) 
               → ∀ {α : Type} (m : ⟨ M ⟩ α) → (bind M Id M b) m (id law-id) ≡ m
    lawFunctor2 (inj₁ IdentTC) IdentB m = refl
    lawFunctor2 (inj₂ (IxMonadTC i j)) FunctorB m = law-left-id monad m

    
    lawMorph1 : ∀ (M N : TyCons) 
              → (B[ M , Id ]▷ N → B[ Id , M ]▷ N)
    lawMorph1 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph1 (inj₁ IdentTC) (inj₂ (IxMonadTC k .k)) ReturnB = ReturnB
    lawMorph1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (lift ())
    lawMorph1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) FunctorB = ApplyB

    lawMorph2 : ∀ (M N : TyCons) 
              → (B[ Id , M ]▷ N → B[ M , Id ]▷ N)
    lawMorph2 (inj₁ IdentTC) (inj₁ IdentTC) IdentB = IdentB
    lawMorph2 (inj₁ IdentTC) (inj₂ (IxMonadTC k .k)) ReturnB = ReturnB
    lawMorph2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (lift ())
    lawMorph2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) ApplyB = FunctorB
    
    lawMorph3 : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷ N) (b₂ : B[ Id , M ]▷ N)
              → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩ β) 
              → (bind M Id N b₁) (f v) (id law-id) ≡ (bind Id M N b₂) (id law-id v) f
    lawMorph3 (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB v f = refl
    lawMorph3 (inj₁ IdentTC) (inj₂ (IxMonadTC k .k)) ReturnB ReturnB v f = refl
    lawMorph3 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (lift ()) b₂ v f
    lawMorph3 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) FunctorB ApplyB v f = begin
      bindFunctor monad (f v) (id law-id) 
        ≡⟨ refl ⟩
      mBind monad (f v) (λ a → mReturn monad (id law-id a))
        ≡⟨ refl ⟩
      mBind monad (f v) (mReturn monad)
        ≡⟨ law-left-id monad (f v) ⟩
      f v
        ≡⟨ sym (law-right-id monad (id law-id v) f) ⟩
      mBind monad (mReturn monad (id law-id v)) f
        ≡⟨ refl ⟩
      bindApply monad (id law-id v) f ∎
    
    lawDiamond1 : ∀ (M N R T : TyCons)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i) , ReturnB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i .i) , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k .k) , ReturnB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC , IdentB , ApplyB) = inj₂ (IxMonadTC i j) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .i) , ReturnB , MonadB) = inj₂ (IxMonadTC i j) , ApplyB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , ApplyB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j) , ApplyB , FunctorB) = inj₂ (IxMonadTC i j) , FunctorB , ApplyB
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , ApplyB , lift ())
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .i .j) , ApplyB , MonadB) = inj₂ (IxMonadTC i l) , MonadB , ApplyB
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , FunctorB , lift ())
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j) , FunctorB , FunctorB) = inj₁ IdentTC , IdentB , FunctorB
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , FunctorB , lift ())
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .i .j) , FunctorB , MonadB) = inj₂ (IxMonadTC j l) , ApplyB , MonadB
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .l) , MonadB , lift ())
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .i .l) , MonadB , FunctorB) = inj₂ (IxMonadTC j l) , FunctorB , MonadB
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .l) , MonadB , lift ())
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₂ (IxMonadTC o p)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond1 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .l n)) (inj₂ (IxMonadTC .i .n)) (inj₂ (IxMonadTC .i .l) , MonadB , MonadB) = inj₂ (IxMonadTC j n) , MonadB , MonadB
    
    lawDiamond2 : ∀ (M N R T : TyCons)
                → (∃ λ(S : TyCons) → B[ N , R ]▷ S × B[ M , S ]▷ T)
                → (∃ λ(P : TyCons) → B[ M , N ]▷ P × B[ P , R ]▷ T)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i) , ReturnB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i .i) , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , ApplyB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j) , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j) , FunctorB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j) , FunctorB , ApplyB) = inj₂ (IxMonadTC i j) , ApplyB , FunctorB
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .l) , MonadB , lift ())
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .i .l) , MonadB , ApplyB) = inj₂ (IxMonadTC i j) , ApplyB , MonadB
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , lift ())
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC k .k) , ReturnB , lift ())
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ (IxMonadTC i j) , FunctorB , FunctorB
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .j .j) , ReturnB , MonadB) = inj₂ (IxMonadTC i j) , FunctorB , FunctorB
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .k .l) , ApplyB , lift ())
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .j .l) , ApplyB , MonadB) = inj₂ (IxMonadTC i j) , FunctorB , MonadB
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .k .l) , FunctorB , lift ())
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .l)) (inj₂ (IxMonadTC .j .l) , FunctorB , MonadB) = inj₂ (IxMonadTC i l) , MonadB , FunctorB
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₁ IdentTC) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC .l n)) (inj₁ IdentTC) (inj₂ (IxMonadTC .k .n) , MonadB , lift ())
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC m n)) (inj₂ (IxMonadTC o p)) (inj₁ IdentTC , lift () , b₂)
    lawDiamond2 (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j l)) (inj₂ (IxMonadTC .l n)) (inj₂ (IxMonadTC .i .n)) (inj₂ (IxMonadTC .j .n) , MonadB , MonadB) = inj₂ (IxMonadTC i l) , MonadB , MonadB


    law-right-idF : ∀ {i j} {M : Ixs → Ixs → TyCon} 
            → (monad : IxMonad Ixs M) 
            → ∀ {α β γ : Type} 
            → (f : α → β) → (k : β → M i j γ) 
            → (λ x → mBind monad (mReturn monad (f x)) k) ≡ (λ x → k (f x))
    law-right-idF monad f k = fun-ext (λ x → law-right-id monad (f x) k)
    
    law-assoc : ∀ (M N P R T S : TyCons) 
               (b₁ : B[ M , N ]▷ P) (b₂ : B[ P , R ]▷ T) 
               (b₃ : B[ N , R ]▷ S) (b₄ : B[ M , S ]▷ T)
             → ∀ {α β γ : Type} (m : ⟨ M ⟩ α) (f : α → ⟨ N ⟩ β) (g : β → ⟨ R ⟩ γ)
             → (bind P R T b₂) ((bind M N P b₁) m f) g ≡ (bind M S T b₄) m (λ x → (bind N R S b₃) (f x) g)
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) IdentB IdentB IdentB IdentB m f g = refl
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) IdentB IdentB ReturnB (lift ()) m f g
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) IdentB ReturnB IdentB ReturnB m f g = refl
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC x x₁)) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i .i)) IdentB ReturnB ReturnB ApplyB m f g = begin
      bindReturn monad (bindId m f) g 
        ≡⟨ refl ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (law-right-id monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC .k .l)) (inj₂ (IxMonadTC .k .l)) IdentB ApplyB ApplyB ApplyB m f g = begin
      bindApply monad (bindId m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (law-right-id monad m (λ x → mBind monad (mReturn monad (f x)) g)) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    law-assoc (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) R T S (lift ()) b₂ b₃ b₄ m f g
    law-assoc (inj₂ (IxMonadTC i j)) N (inj₁ IdentTC) R T S (lift ()) b₂ b₃ b₄ m f g
    law-assoc M N (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    law-assoc M N (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) S b₁ (lift ()) b₃ b₄ m f g
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (inj₁ IdentTC) ReturnB FunctorB IdentB ReturnB m f g = begin
      bindFunctor monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn  monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ law-right-id monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ refl ⟩
      bindReturn monad m (λ x → bindId (f x) g) ∎
    law-assoc (inj₂ (IxMonadTC o p)) (inj₁ IdentTC) (inj₂ (IxMonadTC .o .p)) (inj₁ IdentTC) (inj₂ (IxMonadTC .o .p)) (inj₁ IdentTC) FunctorB FunctorB IdentB FunctorB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a))
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ a → mBind monad (mReturn monad (f a)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (law-right-idF monad f (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ a → mReturn monad (g (f a)))
        ≡⟨ refl ⟩
      bindFunctor monad m (λ x → bindId (f x) g) ∎
    law-assoc M (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC o p)) (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    law-assoc M (inj₂ (IxMonadTC o p)) (inj₂ (IxMonadTC i j)) R (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) b₁ b₂ (lift ()) b₄ m f g
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (inj₂ (IxMonadTC .i .i)) ReturnB FunctorB ReturnB ApplyB m f g = begin
      bindFunctor monad (bindReturn monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) (λ a → mReturn monad (g a))
        ≡⟨ law-right-id monad (f m) (λ a → mReturn monad (g a)) ⟩
      mReturn monad (g (f m))
        ≡⟨ sym (law-right-id monad m ((λ x → mReturn monad (g (f x))))) ⟩
      mBind monad (mReturn monad m) (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindReturn monad (f x) g) ∎
    law-assoc (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i y)) (inj₂ (IxMonadTC .i .y)) (inj₂ (IxMonadTC .i .y)) ReturnB MonadB ApplyB ApplyB m f g = begin
      bindMonad monad (bindReturn monad m f) g
        ≡⟨ refl ⟩
      mBind monad (mReturn monad (f m)) g
        ≡⟨ sym (law-right-id monad m ((λ x → mBind monad (mReturn monad (f x)) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindApply monad (f x) g) ∎
    law-assoc (inj₁ IdentTC) (inj₂ (IxMonadTC x y)) (inj₂ (IxMonadTC .x .y)) (inj₁ IdentTC) (inj₂ (IxMonadTC .x .y)) (inj₂ (IxMonadTC .x .y)) ApplyB FunctorB FunctorB ApplyB m f g = begin
      bindFunctor monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) (λ a → mReturn monad (g a)) 
        ≡⟨ cong (λ x → mBind monad x (λ a → mReturn monad (g a)) ) (law-right-id monad m f) ⟩
      mBind monad (f m) (λ a → mReturn monad (g a))
        ≡⟨ sym (law-right-id monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindFunctor monad (f x) g) ∎
    law-assoc (inj₁ IdentTC) (inj₂ (IxMonadTC x y)) (inj₂ (IxMonadTC .x .y)) (inj₂ (IxMonadTC .y j)) (inj₂ (IxMonadTC .x .j)) (inj₂ (IxMonadTC .x .j)) ApplyB MonadB MonadB ApplyB m f g = begin
      bindMonad monad (bindApply monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad (mReturn monad m) f) g 
        ≡⟨ cong (λ x → mBind monad x g) (law-right-id monad m f) ⟩
      mBind monad (f m) g
        ≡⟨ sym (law-right-id monad m ((λ x → mBind monad (f x) g))) ⟩
      mBind monad (mReturn monad m) (λ x → mBind monad (f x) g)
        ≡⟨ refl ⟩
      bindApply monad m (λ x → bindMonad monad (f x) g) ∎
    law-assoc (inj₂ (IxMonadTC u v)) (inj₁ IdentTC) (inj₂ (IxMonadTC .u .v)) (inj₁ IdentTC) (inj₂ (IxMonadTC .u .v)) (inj₂ (IxMonadTC .v .v)) FunctorB FunctorB ReturnB MonadB m f g = begin
      bindFunctor monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m (λ a → mReturn monad (f a)) (λ a → mReturn monad (g a))) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) (λ a → mReturn monad (g a)) )
        ≡⟨ cong (λ x → mBind monad m x) (fun-ext (λ x → law-right-id monad (f x) ((λ a → mReturn monad (g a))))) ⟩
      mBind monad m (λ x → mReturn monad (g (f x)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindReturn monad (f x) g) ∎
    law-assoc (inj₂ (IxMonadTC u v)) (inj₁ IdentTC) (inj₂ (IxMonadTC .u .v)) (inj₂ (IxMonadTC .v y)) (inj₂ (IxMonadTC .u .y)) (inj₂ (IxMonadTC .v .y)) FunctorB MonadB ApplyB MonadB m f g = begin
      bindMonad monad (bindFunctor monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m (λ a → mReturn monad (f a))) g 
        ≡⟨ sym (mLawAssoc monad m ((λ a → mReturn monad (f a))) g) ⟩
      mBind monad m (λ x → mBind monad (mReturn monad (f x)) g)
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindApply monad (f x) g) ∎
    law-assoc (inj₂ (IxMonadTC u v)) (inj₂ (IxMonadTC .v t)) (inj₂ (IxMonadTC .u .t)) (inj₁ IdentTC) (inj₂ (IxMonadTC .u .t)) (inj₂ (IxMonadTC .v .t)) MonadB FunctorB FunctorB MonadB m f g = begin
      bindFunctor monad (bindMonad monad m f) g 
        ≡⟨ refl ⟩
      mBind monad (mBind monad m f) (λ a → mReturn monad (g a)) 
        ≡⟨ sym (mLawAssoc monad m f ((λ a → mReturn monad (g a)))) ⟩
      mBind monad m (λ x → mBind monad (f x) (λ a → mReturn monad (g a)))
        ≡⟨ refl ⟩
      bindMonad monad m (λ x → bindFunctor monad (f x) g) ∎
    law-assoc (inj₂ (IxMonadTC u v)) (inj₂ (IxMonadTC .v t)) (inj₂ (IxMonadTC .u .t)) (inj₂ (IxMonadTC .t y)) (inj₂ (IxMonadTC .u .y)) (inj₂ (IxMonadTC .v .y)) MonadB MonadB MonadB MonadB m f g = begin
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
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (IdentB , IdentB , IdentB , ReturnB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) U (IdentB , IdentB , lift () , b₄)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) T U (IdentB , lift () , b₃ , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) S T U (lift () , b₂ , b₃ , b₄)
    lawClosure (inj₂ (IxMonadTC i j)) N (inj₁ IdentTC) S T U (lift () , b₂ , b₃ , b₄)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (ReturnB , IdentB , IdentB , lift ())
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₂ y) U (ReturnB , IdentB , lift () , b₄)
    lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC k l)) T U (ReturnB , lift () , b₃ , b₄)
    lawClosure (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC) T (inj₁ IdentTC) (ApplyB , IdentB , b₃ , lift ())
    lawClosure (inj₁ IdentTC) (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i .i)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (ApplyB , IdentB , ReturnB , FunctorB) = ReturnB
    lawClosure (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j)) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC k l)) T U (ApplyB , lift () , b₃ , b₄)
    lawClosure (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) S (inj₁ IdentTC) (inj₁ IdentTC) (FunctorB , b₂ , IdentB , lift ())
    lawClosure (inj₂ (IxMonadTC i .i)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (FunctorB , ReturnB , IdentB , FunctorB) = ReturnB
    lawClosure (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
    lawClosure (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) S (inj₂ (IxMonadTC k l)) U (FunctorB , b₂ , lift () , b₄)
    lawClosure (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j k)) (inj₂ (IxMonadTC .i .k)) S T (inj₁ IdentTC) (MonadB , b₂ , b₃ , lift ())
    lawClosure (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i .i)) (inj₂ (IxMonadTC .i .i)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .i)) (MonadB , ReturnB , ReturnB , FunctorB) = ReturnB
    lawClosure (inj₂ (IxMonadTC i .i)) (inj₂ (IxMonadTC .i k)) (inj₂ (IxMonadTC .i .k)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .k)) (inj₂ (IxMonadTC .i .k)) (MonadB , ReturnB , FunctorB , FunctorB) = ApplyB
    lawClosure (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j .j)) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .i .j)) (inj₁ IdentTC) (inj₂ (IxMonadTC .i .j)) (MonadB , FunctorB , ReturnB , FunctorB) = FunctorB
    lawClosure (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC .j k)) (inj₂ (IxMonadTC .i .k)) (inj₂ (IxMonadTC .i .j)) (inj₂ (IxMonadTC .j .k)) (inj₂ (IxMonadTC .i .k)) (MonadB , FunctorB , FunctorB , FunctorB) = MonadB
