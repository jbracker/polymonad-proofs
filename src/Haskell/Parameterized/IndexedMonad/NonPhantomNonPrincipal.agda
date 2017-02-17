 
module Haskell.Parameterized.IndexedMonad.NonPhantomNonPrincipal where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Function
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Vec hiding ( _>>=_ ; _∈_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Haskell.Monad renaming ( mBind to monadBind ; mReturn to monadReturn )
open import Haskell.Monad.Polymonad
open import Haskell.Monad.Principal
open import Haskell.Monad.Unionable
open import Polymonad.Definition
open import Polymonad.Principal
open import Polymonad.Unionable
open import Haskell.Parameterized.IndexedMonad
open import Haskell.Parameterized.IndexedMonad.DynState
open import Haskell.Parameterized.IndexedMonad.Polymonad
open import Haskell.Parameterized.PhantomIndices 

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

negMap : ∀ {ℓ₁ ℓ₂} {P : Set ℓ₁} {Q : Set ℓ₂} → (Q → P) → ¬ P → ¬ Q
negMap f ¬P Q = ¬P (f Q)

DynStateMonad→Principal : PrincipalPM (IxMonad→Polymonad DynStateMonad)
DynStateMonad→Principal F (M , M' , MM∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
DynStateMonad→Principal F (M , M' , MM∈F) (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ = idTC , IdentB , {!!} , morph₁
DynStateMonad→Principal F (M , M' , MM∈F) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ = {!!}
DynStateMonad→Principal F (M , M' , MM∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = {!!} , {!!} , {!!} , {!!}

DynStateMonad→¬Principal : (NPI : NonPhantomIndices (Type ∷ Type ∷ []) LiftDynState)
                         → ¬ ( proj₁ NPI ≡ proj₁ (proj₂ NPI) )
                         → ¬ PrincipalPM (IxMonad→Polymonad DynStateMonad)
DynStateMonad→¬Principal (I , J , K , L , (lift NPI')) ¬I≡J princ = {!!}
  where
    NPI : ¬ DynState I J ≡ DynState K L
    NPI = negMap (liftDynStateShiftEq' {ℓ = lsuc lzero}) NPI'
    
    TyCons = IdTyCons ⊎ IxMonadTyCons Type
    
    pm = IxMonad→Polymonad DynStateMonad
    
    F : SubsetOf (TyCons × TyCons)
    F (inj₁ IdentTC , inj₁ IdentTC) = Lift ⊤
    F (inj₁ IdentTC , inj₂ M') = Lift ⊤
    F (inj₂ M , M') = Lift ⊥
    
    p : {k l : Type} → B[ idTC , idTC ] pm ▷ inj₂ (IxMonadTC k l) → k ≡ l
    p {k = k} {l = .k} ReturnB = refl
    
    q : (k l : Type) → k ≡ l → B[ idTC , idTC ] pm ▷ inj₂ (IxMonadTC k l)
    q k .k refl = ReturnB

    p2 : {k l s t : Type} → B[ inj₂ (IxMonadTC s t) , idTC ] pm ▷ inj₂ (IxMonadTC k l) → s ≡ k × t ≡ l
    p2 FunctorB = refl , refl

    morph₁ : (M M' : TyCons) 
           → (M , M') ∈ F
           → B[ M , M' ] pm ▷ idTC
    morph₁ (inj₁ IdentTC) (inj₁ IdentTC) (lift tt) = IdentB
    morph₁ (inj₁ IdentTC) (inj₂ (IxMonadTC S T)) (lift tt) = {!!}
    morph₁ (inj₂ M) M' (lift ())
    {-
    morph₂ : (M M' : TyCons) 
           → (M , M') ∈ F
           → B[ M , M' ] pm ▷ (inj₂ (IxMonadTC I J))
    morph₂ (inj₁ IdentTC) (inj₁ IdentTC) (lift tt) = q I J {!!}
    morph₂ (inj₁ IdentTC) (inj₂ M') (lift ())
    morph₂ (inj₂ M) M' (lift ())
    -}
    bottom : ⊥
    bottom with princ F (idTC , idTC , lift tt) idTC idTC morph₁ morph₁
    bottom | inj₁ IdentTC , IdentB , IdentB , morph = {!!}
    bottom | inj₂ (IxMonadTC S T) , lift () , lift () , morph

    {-
    bottom : ⊥
    bottom with princ F (idTC , idTC , lift tt) (inj₂ (IxMonadTC I J)) (inj₂ (IxMonadTC I J)) morph₂ morph₂
    bottom | inj₁ IdentTC , b₁ , b₂ , morph = ¬I≡J (p b₂)
    bottom | inj₂ (IxMonadTC S T) , b₁ , b₂ , morph with p2 b₁
    bottom | inj₂ (IxMonadTC .I .J) , FunctorB , FunctorB , morph | refl , refl = ¬I≡J (p (morph idTC idTC (lift tt)))
    -}
    
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
