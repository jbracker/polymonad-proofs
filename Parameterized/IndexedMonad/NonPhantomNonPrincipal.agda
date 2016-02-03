 
module Parameterized.IndexedMonad.NonPhantomNonPrincipal where

-- Stdlib
open import Level
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
--open import Data.Vec hiding ( _>>=_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Monad renaming ( mBind to monadBind ; mReturn to monadReturn )
open import Monad.Polymonad
open import Monad.Principal
open import Monad.Unionable
open import Polymonad
open import Polymonad.Principal
open import Polymonad.Unionable
open import Parameterized.IndexedMonad
open import Parameterized.IndexedMonad.Polymonad
open import Parameterized.PhantomIndices 

open IxMonad renaming (bind to mBind; return to mReturn; lawIdR to mLawIdR ; lawIdL to mLawIdL ; lawAssoc to mLawAssoc ) hiding (_>>=_)
{-
PhantomIxMonad→Monad : ∀ {Ixs} {M}
                     → ¬ (PhantomIndices (Ixs ∷ Ixs ∷ []) M) 
                     → (ixMonad : IxMonad Ixs M)
                     → ¬ (PrincipalPM (IxMonad→Polymonad ixMonad))
PhantomIxMonad→Monad {Ixs = Ixs} {M = M} ¬Phantom ixMonad princ = ¬Phantom ({!!} , (λ {i j : Ixs} → {!!}))
    -}
{-
PhantomIndices : ∀ {n} (ts : Vec Set n) → (M : ParamTyCon ts) → Set₁
PhantomIndices ts M = ∃ λ(K : TyCon) → ∀Indices ts M (λ X → X ≡ K)

PrincipalPM : ∀ {TyCons : Set} {Id : TyCons} →  Polymonad TyCons Id → Set₁
PrincipalPM {TyCons} {Id} pm 
  = (F : SubsetOf (TyCons × TyCons))
  → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F)
  → (M₁ M₂ : TyCons)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₁)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₂)
  → ∃ λ(M̂ : TyCons) 
  → B[ M̂ , Id ] pm ▷ M₁ 
  × B[ M̂ , Id ] pm ▷ M₂ 
  × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)
-}


record DState (i : Type) (j : Type) (α : Type) : Type where
  constructor DStateCon
  field
    stateFun : i → j × α

runDState : {i j α : Type} → DState i j α → i → j × α
runDState (DStateCon sf) i = sf i

execDState : {i j α : Type} → DState i j α → i → j
execDState ma i = proj₁ (runDState ma i)

evalDState : {i j α : Type} → DState i j α → i → α
evalDState ma i = proj₂ (runDState ma i)

DynStateMonad : IxMonad Type DState
DynStateMonad = record
  { _>>=_ = λ ma f → DStateCon (λ i → let j , a = runDState ma i in runDState (f a) j)
  ; return = λ a → DStateCon (λ s → s , a)
  ; lawIdR = λ a k → refl
  ; lawIdL = λ m → refl
  ; lawAssoc = λ m f g → refl 
  }

DynStateMonad→Principal : PrincipalPM (IxMonad→Polymonad DynStateMonad)
DynStateMonad→Principal F (M , M' , MM∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
DynStateMonad→Principal F (M , M' , MM∈F) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ = idTC , IdentB , {!!} , morph₁
DynStateMonad→Principal F (M , M' , MM∈F) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ = {!!}
DynStateMonad→Principal F (M , M' , MM∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = {!!} , {!!} , {!!} , {!!}

DynStateMonad→¬Principal : (∃ λ(i : Type) → ∃ λ(j : Type) → ¬ i ≡ j ) → ¬ PrincipalPM (IxMonad→Polymonad DynStateMonad)
DynStateMonad→¬Principal (i , j , ¬i≡j) princ = bottom
  where
    TyCons = IdTyCons ⊎ IxMonadTyCons Type
    
    pm = IxMonad→Polymonad DynStateMonad
    
    F : SubsetOf (TyCons × TyCons)
    F (inj₁ IdentTC , inj₁ IdentTC) = Lift ⊤
    F (inj₁ IdentTC , inj₂ M') = Lift ⊥
    F (inj₂ M , M') = Lift ⊥

    morph₁ : (M M' : TyCons) 
           → (M , M') ∈ F
           → B[ M , M' ] pm ▷ idTC
    morph₁ (inj₁ IdentTC) (inj₁ IdentTC) (lift tt) = IdentB
    morph₁ (inj₁ IdentTC) (inj₂ M') (lift ())
    morph₁ (inj₂ M) M' (lift ())

    morph₂ : (M M' : TyCons) 
           → (M , M') ∈ F
           → B[ M , M' ] pm ▷ (inj₂ (IxMonadTC i j))
    morph₂ (inj₁ IdentTC) (inj₁ IdentTC) (lift tt) = {!!}
    morph₂ (inj₁ IdentTC) (inj₂ M') (lift ())
    morph₂ (inj₂ M) M' (lift ())
    
    p : {k l : Type} → B[ idTC , idTC ] pm ▷ inj₂ (IxMonadTC k l) → k ≡ l
    p {k = k} {l = .k} ReturnB = refl
    
    q : (k l : Type) → k ≡ l → B[ idTC , idTC ] pm ▷ inj₂ (IxMonadTC k l)
    q k .k refl = ReturnB
    
    bottom : ⊥
    bottom with princ F (idTC , idTC , lift tt) idTC (inj₂ (IxMonadTC i j)) morph₁ morph₂
    bottom | inj₁ IdentTC , IdentB , b , morph = ¬i≡j (p b)
    bottom | inj₂ (IxMonadTC .i .j) , lift () , FunctorB , morph

    
{-
PrincipalPM : ∀ {TyCons : Set} {Id : TyCons} →  Polymonad TyCons Id → Set₁
PrincipalPM {TyCons} {Id} pm 
  = (F : SubsetOf (TyCons × TyCons))
  → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F)
  → (M₁ M₂ : TyCons)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₁)
  → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M₂)
  → ∃ λ(M̂ : TyCons) 
  → B[ M̂ , Id ] pm ▷ M₁ 
  × B[ M̂ , Id ] pm ▷ M₂ 
  × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)
-}
