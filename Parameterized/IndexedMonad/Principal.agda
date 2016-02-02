 
module Parameterized.IndexedMonad.Principal where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.Principal
open import Parameterized.IndexedMonad
open import Parameterized.IndexedMonad.Polymonad

open IxMonad renaming (bind to mBind; return to mReturn; lawAssoc to mLawAssoc)
open Polymonad.Polymonad

-- -----------------------------------------------------------------------------
-- Indexed polymonads are principal (unproven)
-- -----------------------------------------------------------------------------
IxMonad→PrincipalPolymonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
                           → Decidable {A = Ixs} _≡_
                           → (monad : IxMonad Ixs M)
                           → ((PS : (IdTyCons ⊎ IxMonadTyCons Ixs) × (IdTyCons ⊎ IxMonadTyCons Ixs)) → (F : SubsetOf ((IdTyCons ⊎ IxMonadTyCons Ixs) × (IdTyCons ⊎ IxMonadTyCons Ixs))) → Dec (PS ∈ F))
                           → PrincipalPM (IxMonad→Polymonad monad)
IxMonad→PrincipalPolymonad {Ixs = Ixs} _∼_ monad _∈?_ = princ
  where
    TyCons = IdTyCons ⊎ IxMonadTyCons Ixs
    
    pm = IxMonad→Polymonad monad
    
    mTC : Ixs → Ixs → TyCons
    mTC i j = inj₂ (IxMonadTC i j)
    
    ¬MN∈F : (F : SubsetOf (TyCons × TyCons)) 
          → ((M N : TyCons) → (M , N) ∈ F → B[ M , N ] pm ▷ idTC)
          → (M N : TyCons) → (∃ λ(P : IxMonadTyCons Ixs) → (M ≡ inj₂ P ⊎ N ≡ inj₂ P)) → ¬ ((M , N) ∈ F)
    ¬MN∈F F morphId .(inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (IxMonadTC i j , inj₁ refl) MN∈F = morphId (mTC i j) idTC MN∈F
    ¬MN∈F F morphId .(inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) (IxMonadTC i j , inj₁ refl) MN∈F = morphId (mTC i j) (mTC k l) MN∈F
    ¬MN∈F F morphId (inj₁ IdentTC) .(inj₂ (IxMonadTC i j)) (IxMonadTC i j , inj₂ refl) MN∈F = morphId idTC (mTC i j) MN∈F
    ¬MN∈F F morphId (inj₂ (IxMonadTC i j)) .(inj₂ (IxMonadTC k l)) (IxMonadTC k l , inj₂ refl) MN∈F = morphId (mTC i j) (mTC k l) MN∈F

    ¬returnB : (k l : Ixs)
              → ¬ k ≡ l 
              → ¬ B[ idTC , idTC ] pm ▷ (inj₂ (IxMonadTC k l))
    ¬returnB k .k ¬k≡l ReturnB = ¬k≡l refl
    
    ¬applyB : (k l i j : Ixs)
              → (¬ i ≡ k ⊎ ¬ j ≡ l)
              → ¬ B[ idTC , mTC k l ] pm ▷ mTC i j
    ¬applyB .i .j i j (inj₁ ¬i≡k) ApplyB = ¬i≡k refl
    ¬applyB .i .j i j (inj₂ ¬j≡l) ApplyB = ¬j≡l refl
    
    ¬functorB : (k l i j : Ixs)
              → (¬ i ≡ k ⊎ ¬ j ≡ l)
              → ¬ B[ mTC k l , idTC ] pm ▷ mTC i j
    ¬functorB .i .j i j (inj₁ ¬i≡k) FunctorB = ¬i≡k refl
    ¬functorB .i .j i j (inj₂ ¬j≡l) FunctorB = ¬j≡l refl
    
    ¬monadB : (k l s t i j : Ixs)
              → ((¬ i ≡ k ⊎ ¬ j ≡ t) ⊎ ¬ l ≡ s)
              → ¬ B[ mTC k l , mTC s t ] pm ▷ mTC i j
    ¬monadB k l .l t .k .t (inj₁ (inj₁ ¬i≡k)) MonadB = ¬i≡k refl
    ¬monadB k l .l t .k .t (inj₁ (inj₂ ¬j≡t)) MonadB = ¬j≡t refl
    ¬monadB k l .l t .k .t (inj₂ ¬l≡s) MonadB = ¬l≡s refl

    ¬MN∈F' : ∀ {i j : Ixs}
           → (F : SubsetOf (TyCons × TyCons)) 
           → ((M N : TyCons) → (M , N) ∈ F → B[ M , N ] pm ▷ mTC i j)
           → (M N : TyCons) 
           → ( ∃ λ(k : Ixs) → ∃ λ(l : Ixs) 
             → ( ( M ≡ mTC k l × ¬ i ≡ k )
               ⊎ ( N ≡ mTC k l × ¬ j ≡ l )
               )
             ) 
             ⊎ (M ≡ idTC × N ≡ idTC × ¬ i ≡ j)
           → ¬ ((M , N) ∈ F)
    ¬MN∈F' F morph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ (k , l , inj₁ ((), ¬i≡k))) MN∈F
    ¬MN∈F' F morph (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ (k , l , inj₂ ((), ¬j≡l))) MN∈F
    ¬MN∈F' {i = i} {j = j} F morph (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (refl , refl , ¬i≡j)) MN∈F 
      = ¬returnB i j ¬i≡j (morph idTC idTC MN∈F)
    ¬MN∈F' F morph (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₁ (k , l , inj₁ (() , ¬i≡k))) MN∈F
    ¬MN∈F' {i = i} {j = j} F morph (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) (inj₁ (.k , .l , inj₂ (refl , ¬j≡l))) MN∈F
      = ¬applyB k l i j (inj₂ ¬j≡l) (morph idTC (mTC k l) MN∈F)
    ¬MN∈F' F morph (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) (inj₂ (refl , () , ¬i≡j)) MN∈F
    ¬MN∈F' {i = i} {j = j} F morph (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ (.k , .l , inj₁ (refl , ¬i≡k))) MN∈F
      = ¬functorB k l i j (inj₁ ¬i≡k) (morph (mTC k l) idTC MN∈F)
    ¬MN∈F' F morph (inj₂ (IxMonadTC k l)) (inj₁ IdentTC) (inj₁ (s , t , inj₂ (() , ¬i≡k))) MN∈F
    ¬MN∈F' F morph (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) (inj₂ (() , refl , ¬i≡j)) MN∈F
    ¬MN∈F' {i = i} {j = j} F morph (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC s t)) (inj₁ (.k , .l , inj₁ (refl , ¬i≡k))) MN∈F
      = ¬monadB k l s t i j (inj₁ (inj₁ ¬i≡k)) (morph (mTC k l) (mTC s t) MN∈F)
    ¬MN∈F' {i = i} {j = j} F morph (inj₂ (IxMonadTC k l)) (inj₂ (IxMonadTC s t)) (inj₁ (.s , .t , inj₂ (refl , ¬j≡t))) MN∈F 
      = ¬monadB k l s t i j (inj₁ (inj₂ ¬j≡t)) (morph (mTC k l) (mTC s t) MN∈F)
    ¬MN∈F' F morph (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k' l')) (inj₂ (() , () , ¬i≡j)) MN∈F
    
    ¬true→false : ∀ {x : Bool} → ¬ (x ≡ true) → x ≡ false
    ¬true→false {true} ¬x≡true = ⊥-elim (¬x≡true refl)
    ¬true→false {false} ¬x≡true = refl

    emptyF : (F : SubsetOf (TyCons × TyCons))
           → ¬ (idTC , idTC) ∈ F
           → ((M N : TyCons) → (M , N) ∈ F → B[ M , N ] pm ▷ idTC)
           → (M N : TyCons) → ¬ (M , N) ∈ F
    emptyF F ¬II∈F morph (inj₁ IdentTC) (inj₁ IdentTC) = ¬II∈F
    emptyF F ¬II∈F morph (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) = ¬MN∈F F morph idTC (mTC k l) ((IxMonadTC k l) , (inj₂ refl))
    emptyF F ¬II∈F morph (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) = ¬MN∈F F morph (mTC i j) idTC ((IxMonadTC i j) , (inj₁ refl))
    emptyF F ¬II∈F morph (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) = ¬MN∈F F morph (mTC i j) (mTC k l) ((IxMonadTC i j) , (inj₁ refl))
    
    II∈F→¬morphMij : ∀ {Ixs : Set} {N : Ixs → Ixs → TyCon}
                   → (monad : IxMonad Ixs N)
                   → (i j : Ixs) → ¬ (i ≡ j)
                  → (F : SubsetOf ((IdTyCons ⊎ IxMonadTyCons Ixs) × (IdTyCons ⊎ IxMonadTyCons Ixs))) 
                  → (idTC , idTC) ∈ F
                  → ¬ ((M M' : IdTyCons ⊎ IxMonadTyCons Ixs) → (M , M') ∈ F → B[ M , M' ] (IxMonad→Polymonad monad) ▷ inj₂ (IxMonadTC i j))
    II∈F→¬morphMij monad i  j ¬i≡j F II∈F morph with morph idTC idTC II∈F
    II∈F→¬morphMij monad i .i ¬i≡j F II∈F morph | ReturnB = ¬i≡j refl

    IM∈F→¬morphMij : ∀ {Ixs : Set} {N : Ixs → Ixs → TyCon}
                   → (monad : IxMonad Ixs N)
                   → (i j k l : Ixs) → (¬ (i ≡ k) ⊎ ¬ (j ≡ l))
                   → (F : SubsetOf ((IdTyCons ⊎ IxMonadTyCons Ixs) × (IdTyCons ⊎ IxMonadTyCons Ixs))) 
                   → (idTC , inj₂ (IxMonadTC k l)) ∈ F
                   → ¬ ((M M' : IdTyCons ⊎ IxMonadTyCons Ixs) → (M , M') ∈ F → B[ M , M' ] (IxMonad→Polymonad monad) ▷ inj₂ (IxMonadTC i j))
    IM∈F→¬morphMij monad i j k l unequal F IM∈F morph with morph idTC (inj₂ (IxMonadTC k l)) IM∈F
    IM∈F→¬morphMij monad i j .i .j (inj₁ ¬i≡k) F IM∈F morph | ApplyB = ¬i≡k refl
    IM∈F→¬morphMij monad i j .i .j (inj₂ ¬j≡l) F IM∈F morph | ApplyB = ¬j≡l refl
    
    ¬morphId : (F : SubsetOf (TyCons × TyCons)) 
             → (∃ λ(P : TyCons) → ¬ P ≡ idTC × ∃ λ(S : TyCons) → (P , S) ∈ F ⊎ (S , P) ∈ F) 
             → ¬ ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ idTC)
    ¬morphId F (inj₁ IdentTC         , ¬P≡Id , S , inj₁ PS∈F) morphId = ¬P≡Id refl
    ¬morphId F (inj₂ (IxMonadTC i j) , ¬P≡Id , S , inj₁ PS∈F) morphId = ⊥-elim (morphId (mTC i j) S PS∈F)
    ¬morphId F (inj₁ IdentTC         , ¬P≡Id , S , inj₂ SP∈F) morphId = ¬P≡Id refl
    ¬morphId F (inj₂ (IxMonadTC i j) , ¬P≡Id , inj₁ IdentTC         , inj₂ SP∈F) morphId = morphId idTC (mTC i j) SP∈F
    ¬morphId F (inj₂ (IxMonadTC i j) , ¬P≡Id , inj₂ (IxMonadTC k l) , inj₂ SP∈F) morphId = morphId (mTC k l) (mTC i j) SP∈F
    
    princ : PrincipalPM pm
    princ F PS∈F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
    princ F PS∈F (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) morph₁ morph₂ with (idTC , idTC) ∈? F 
    princ F PS∈F (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) morph₁ morph₂ | yes II∈F = idTC , IdentB , morph₂ idTC idTC II∈F , morph₁
    princ F (P , S , PS∈F) (inj₁ IdentTC) (inj₂ (IxMonadTC k l)) morph₁ morph₂ | no ¬II∈F = ⊥-elim (emptyF F ¬II∈F morph₁ P S PS∈F)
    princ F PS∈F (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ with (idTC , idTC) ∈? F 
    princ F PS∈F (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ | yes II∈F = idTC , morph₁ idTC idTC II∈F , IdentB , morph₂
    princ F (P , S , PS∈F) (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ | no ¬II∈F = ⊥-elim (emptyF F ¬II∈F morph₂ P S PS∈F)
    {-
    princ F ((inj₁ IdentTC , inj₁ IdentTC) , PS∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = solution (i ∼ j) (k ∼ l) (i ∼ k)
      where
        solution : Dec (i ≡ j) → Dec (k ≡ l) → Dec (i ≡ k)
                 → ∃ (λ M̂ 
                     → B[ M̂ , idTC ] pm ▷ inj₂ (IxMonadTC i j)
                     × B[ M̂ , idTC ] pm ▷ inj₂ (IxMonadTC k l)
                     × ((M M' : IdTyCons ⊎ IxMonadTyCons Ixs) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)
                     )
        solution (yes i≡j) (yes k≡l) (yes i≡k)
          = mTC i j , FunctorB , subst₂ (λ K L → B[ mTC i j , idTC ] pm ▷ mTC K L) i≡k (trans (sym i≡j) (trans i≡k k≡l)) FunctorB , morph₁
        solution (yes i≡j) (yes k≡l) (no ¬i≡k) = {!!}
        solution (yes i≡j) (no ¬k≡l) = ⊥-elim (¬MN∈F' F morph₂ idTC idTC (inj₂ (refl , refl , ¬k≡l)) PS∈F)
        solution (no ¬i≡j) = ⊥-elim (¬MN∈F' F morph₁ idTC idTC (inj₂ (refl , refl , ¬i≡j)) PS∈F)
    princ F ((inj₁ x , inj₂ y) , PS∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = {!!}
    princ F ((inj₂ y , S) , PS∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = {!!}
    -}
    princ F (P , S , PS∈F) (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ =
      solution ((mTC i j , idTC) ∈? F) ((idTC , mTC i j) ∈? F) 
               ((mTC k l , idTC) ∈? F) ((idTC , mTC k l) ∈? F)
      where
        solution : Dec ((mTC i j , idTC) ∈ F) → Dec ((idTC , mTC i j) ∈ F)
                 → Dec ((mTC k l , idTC) ∈ F) → Dec ((idTC , mTC k l) ∈ F)
                 → ∃ (λ M̂ 
                     → B[ M̂ , idTC ] pm ▷ inj₂ (IxMonadTC i j)
                     × B[ M̂ , idTC ] pm ▷ inj₂ (IxMonadTC k l)
                     × ((M M' : IdTyCons ⊎ IxMonadTyCons Ixs) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂)
                     )
        solution (yes MijI∈F) IMij∈F MklI∈F IMkl∈F = mTC i j , FunctorB , morph₂ (mTC i j) idTC MijI∈F , morph₁
        solution (no ¬MijI∈F) (yes IMij∈F) MklI∈F IMkl∈F = mTC i j , FunctorB , pmLawMorph2 pm (mTC i j) (mTC k l) (morph₂ idTC (mTC i j) IMij∈F) , morph₁
        solution (no ¬MijI∈F) (no ¬IMij∈F) (yes MklI∈F) IMkl∈F = mTC k l , (morph₁ (mTC k l) idTC MklI∈F) , FunctorB , morph₂
        solution (no ¬MijI∈F) (no ¬IMij∈F) (no ¬MklI∈F) (yes IMkl∈F) = mTC k l , pmLawMorph2 pm (mTC k l) (mTC i j) (morph₁ idTC (mTC k l) IMkl∈F) , FunctorB , morph₂
        solution (no ¬MijI∈F) (no ¬IMij∈F) (no ¬MklI∈F) (no ¬IMkl∈F) = {!!}

-- -----------------------------------------------------------------------------
--
-- -----------------------------------------------------------------------------
IxMonad→¬PrincipalPolymonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon}
                             → (∃ λ(i : Ixs) → ∃ λ(j : Ixs) → ¬ (i ≡ j))
                             → (monad : IxMonad Ixs M)
                             → ¬ (PrincipalPM (IxMonad→Polymonad monad))
IxMonad→¬PrincipalPolymonad {Ixs = Ixs} (i , j , ¬i≡j) monad princ = bottom
  where
    TyCons = IdTyCons ⊎ IxMonadTyCons Ixs
    
    pm = IxMonad→Polymonad monad
    
    mTC : Ixs → Ixs → TyCons
    mTC i j = inj₂ (IxMonadTC i j)
    
    idF : SubsetOf (TyCons × TyCons)
    idF (inj₁ IdentTC , inj₁ IdentTC) = ⊤
    idF (inj₁ IdentTC , inj₂ N) = ⊥
    idF (inj₂ M , N) = ⊥
    
    ¬returnB : (k l : Ixs)
              → ¬ k ≡ l 
              → ¬ B[ idTC , idTC ] pm ▷ (inj₂ (IxMonadTC k l))
    ¬returnB k .k ¬k≡l ReturnB = ¬k≡l refl
    
    morphIJ : (M M' : IdTyCons ⊎ IxMonadTyCons Ixs) 
            → (M , M') ∈ idF
            → B[ M , M' ] pm ▷ mTC i j
    morphIJ (inj₁ IdentTC) (inj₁ IdentTC) tt = {!!}
    morphIJ (inj₁ IdentTC) (inj₂ M) ()
    morphIJ (inj₂ M) M' ()
    
    morphId : (M M' : IdTyCons ⊎ IxMonadTyCons Ixs) 
            → (M , M') ∈ idF 
            → B[ M , M' ] pm ▷ idTC
    morphId (inj₁ IdentTC) (inj₁ IdentTC) tt = IdentB
    morphId (inj₁ IdentTC) (inj₂ M') ()
    morphId (inj₂ M) M' ()
    
    bottom : ⊥
    bottom with princ idF (idTC , idTC , tt) (mTC i j) idTC morphIJ morphId
    bottom | inj₁ IdentTC , b₁ , IdentB , morph = ¬returnB i j ¬i≡j b₁
    bottom | inj₂ (IxMonadTC k l) , b₁ , () , morph

-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

{-
principalPolymonadMonadIxMonadUnion : ∀ {Ixs : Set} {M₁ : TyCon} {M₂ : Ixs → Ixs → TyCon} 
                          → (monad₁ : Monad M₁) → (monad₂ : IxMonad Ixs M₂) 
                          → PrincipalPM (polymonadUnion (Monad→UnionablePolymonad monad₁) (IxMonad→UnionablePolymonad monad₂))
principalPolymonadMonadIxMonadUnion {Ixs = Ixs} monad₁ monad₂ = princ
  where
    
    TyCons = IdTyCons ⊎ (MonadTyCons ⊎ IxMonadTyCons Ixs)
    
    upm₁ = Monad→UnionablePolymonad monad₁
    upm₂ = IxMonad→UnionablePolymonad monad₂

    pm₁ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₁ = upmPolymonad upm₁

    pm₂ : Polymonad (IdTyCons ⊎ IxMonadTyCons Ixs) idTC
    pm₂ = upmPolymonad upm₂
    
    pm : Polymonad TyCons idTC
    pm = polymonadUnion upm₁ upm₂

    mTC₁ : TyCons
    mTC₁ = inj₂ (inj₁ MonadTC)
    
    mTC₂ : Ixs → Ixs → TyCons
    mTC₂ i j = inj₂ (inj₂ (IxMonadTC i j))
    
    contradiction : ∀ {l} {P : Set l} → P → ¬ P → ⊥
    contradiction P ¬P = ¬P P
    
    mixedPrinc : {i j : Ixs} → (F : SubsetOf (TyCons × TyCons)) 
               → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ inj₂ (inj₁ MonadTC))
               → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ inj₂ (inj₂ (IxMonadTC i j)))
               → (∀ (M N : TyCons) → (∃ λ(P : MonadTyCons ⊎ IxMonadTyCons Ixs) → (M ≡ inj₂ P ⊎ N ≡ inj₂ P)) → ¬ ((M , N) ∈ F))
               → ∃ (λ M̂ → B[ M̂ , idTC ] pm ▷ inj₂ (inj₁ MonadTC)
                        × B[ M̂ , idTC ] pm ▷ inj₂ (inj₂ (IxMonadTC i j))
                        × ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
    mixedPrinc {i} {j} F morph₁ morph₂ ¬MN∈F = solution
      where
        newMorph : (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ idTC
        newMorph (inj₁ IdentTC) (inj₁ IdentTC) II∈F = IdentB
        newMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) IM₁∈F = ⊥-elim (contradiction IM₁∈F (¬MN∈F idTC mTC₁ (inj₁ MonadTC , inj₂ refl)))
        newMorph (inj₁ IdentTC) (inj₂ (inj₂ (IxMonadTC i j))) IM₂∈F = ⊥-elim (contradiction IM₂∈F (¬MN∈F idTC (mTC₂ i j) (inj₂ (IxMonadTC i j) , inj₂ refl)))
        newMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) M₁I∈F = ⊥-elim (contradiction M₁I∈F (¬MN∈F mTC₁ idTC (inj₁ MonadTC , inj₁ refl)))
        newMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) M₁M₁∈F = ⊥-elim (contradiction M₁M₁∈F (¬MN∈F mTC₁ mTC₁ (inj₁ MonadTC , inj₁ refl)))
        newMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ (IxMonadTC i j))) M₁M₂∈F = ⊥-elim (contradiction M₁M₂∈F (¬MN∈F mTC₁ (mTC₂ i j) (inj₁ MonadTC , inj₁ refl)))
        newMorph (inj₂ (inj₂ (IxMonadTC i j))) (inj₁ IdentTC) M₂I∈F = ⊥-elim (contradiction M₂I∈F (¬MN∈F (mTC₂ i j) idTC (inj₂ (IxMonadTC i j) , inj₁ refl)))
        newMorph (inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₁ MonadTC)) M₂M₁∈F = ⊥-elim (contradiction M₂M₁∈F (¬MN∈F (mTC₂ i j) mTC₁ (inj₂ (IxMonadTC i j) , inj₁ refl)))
        newMorph (inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₂ (IxMonadTC k l))) M₂M₂∈F = ⊥-elim (contradiction M₂M₂∈F (¬MN∈F (mTC₂ i j) (mTC₂ k l) (inj₂ (IxMonadTC k l) , inj₂ refl)))
        
        solution : ∃ (λ M̂ → B[ M̂ , idTC ] pm ▷ inj₂ (inj₁ MonadTC) 
                          × B[ M̂ , idTC ] pm ▷ inj₂ (inj₂ (IxMonadTC i j)) 
                          × ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
        solution with (idTC , idTC) ∈? F
        solution | yes II∈F = idTC , ReturnB , morph₂ idTC idTC II∈F , newMorph
        solution | no ¬II∈F = idTC , ReturnB , {!!} , newMorph
    
    ¬MN∈F : {i j : Ixs} 
      → (F : SubsetOf (TyCons × TyCons)) 
      → ((M N : TyCons) → (M , N) ∈ F → B[ M , N ] pm ▷ inj₂ (inj₁ MonadTC))
      → ((M N : TyCons) → (M , N) ∈ F → B[ M , N ] pm ▷ inj₂ (inj₂ (IxMonadTC i j)))
      → (M N : TyCons) → (∃ λ(P : MonadTyCons ⊎ IxMonadTyCons Ixs) → (M ≡ inj₂ P ⊎ N ≡ inj₂ P)) → ¬ ((M , N) ∈ F)
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ MonadTC , inj₁ refl) MN∈F = morph₂ mTC₁ idTC MN∈F
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ MonadTC , inj₁ refl) MN∈F = morph₂ mTC₁ mTC₁ MN∈F
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ (IxMonadTC i j))) (inj₁ MonadTC , inj₁ refl) MN∈F = morph₁ mTC₁ (mTC₂ i j) MN∈F
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₂ (IxMonadTC i j))) (inj₁ IdentTC) (inj₂ (IxMonadTC i j) , inj₁ refl) MN∈F = morph₁ (mTC₂ i j) idTC MN∈F
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₁ MonadTC)) (inj₂ (IxMonadTC i j) , inj₁ refl) MN∈F = morph₂ (mTC₂ i j) mTC₁ MN∈F
    ¬MN∈F F morph₁ morph₂ .(inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₂ (IxMonadTC k l))) (inj₂ (IxMonadTC i j) , inj₁ refl) MN∈F = morph₁ (mTC₂ i j) (mTC₂ k l) MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₁ IdentTC) .(inj₂ (inj₁ MonadTC)) (inj₁ MonadTC , inj₂ refl) MN∈F = morph₂ idTC mTC₁ MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₂ (inj₁ MonadTC)) .(inj₂ (inj₁ MonadTC)) (inj₁ MonadTC , inj₂ refl) MN∈F = morph₂ mTC₁ mTC₁ MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₂ (inj₂ (IxMonadTC i j))) .(inj₂ (inj₁ MonadTC)) (inj₁ MonadTC , inj₂ refl) MN∈F = morph₂ (mTC₂ i j) mTC₁ MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₁ IdentTC) .(inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (IxMonadTC i j) , inj₂ refl) MN∈F = morph₁ idTC (mTC₂ i j) MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₂ (inj₁ MonadTC)) .(inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (IxMonadTC i j) , inj₂ refl) MN∈F = morph₁ mTC₁ (mTC₂ i j) MN∈F
    ¬MN∈F F morph₁ morph₂ (inj₂ (inj₂ (IxMonadTC i j))) .(inj₂ (inj₂ (IxMonadTC k l))) (inj₂ (IxMonadTC k l) , inj₂ refl) MN∈F = morph₁ (mTC₂ i j) (mTC₂ k l) MN∈F
    
    princ : PrincipalPM pm
    princ F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
    princ F (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = idTC , IdentB , ReturnB , morph₁
    princ F (inj₁ IdentTC) (inj₂ (inj₂ (IxMonadTC i j))) morph₁ morph₂ = idTC , IdentB , {!!} , morph₁
    princ F (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) morph₁ morph₂ = idTC , ReturnB , IdentB , morph₂
    princ F (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = mTC₁ , FunctorB , FunctorB , morph₁
    princ F (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ (IxMonadTC i j))) morph₁ morph₂ = mixedPrinc F morph₁ morph₂ (¬MN∈F F morph₁ morph₂)
    princ F (inj₂ (inj₂ (IxMonadTC i j))) (inj₁ IdentTC) morph₁ morph₂ with (idTC , idTC) ∈? F
    princ F (inj₂ (inj₂ (IxMonadTC i j))) (inj₁ IdentTC) morph₁ morph₂ | yes II∈F = idTC , morph₁ idTC idTC II∈F , IdentB , morph₂
    princ F (inj₂ (inj₂ (IxMonadTC i j))) (inj₁ IdentTC) morph₁ morph₂ | no ¬II∈F = {!!}
    princ F (inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = 
      let M , b₁ , b₂ , morph = mixedPrinc F morph₂ morph₁ (¬MN∈F F morph₂ morph₁) in M , b₂ , b₁ , morph
    princ F (inj₂ (inj₂ (IxMonadTC i j))) (inj₂ (inj₂ (IxMonadTC k l))) morph₁ morph₂ = mTC₂ i j , FunctorB , {!!} , morph₁
-}
