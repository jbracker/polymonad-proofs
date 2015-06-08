 
module Parameterized.IndexedMonad.Principal where

-- Stdlib
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
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

IxMonad→PrincipalPolymonad : ∀ {Ixs : Set} {M : Ixs → Ixs → TyCon} 
                           → (monad : IxMonad Ixs M)
                           → PrincipalPM (IxMonad→Polymonad monad)
IxMonad→PrincipalPolymonad {Ixs = Ixs} monad = princ
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
    
    princ : PrincipalPM pm
    princ F (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
    princ F (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ with (idTC , idTC) ∈? F
    princ F (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ | yes II∈F = idTC , IdentB , morph₂ idTC idTC II∈F , morph₁
    princ F (inj₁ IdentTC) (inj₂ (IxMonadTC i j)) morph₁ morph₂ | no ¬II∈F = mTC i j , {!!} , FunctorB , (λ M N MN∈F → ⊥-elim (emptyF F ¬II∈F morph₁ M N MN∈F))
    princ F (inj₂ (IxMonadTC i j)) (inj₁ IdentTC) morph₁ morph₂ = idTC , {!!} , {!!} , {!!}
    princ F (inj₂ (IxMonadTC i j)) (inj₂ (IxMonadTC k l)) morph₁ morph₂ = mTC i j , FunctorB , {!!} , morph₁


{-
principalPolymonadMonadIxMonadCompose : ∀ {Ixs : Set} {M₁ : TyCon} {M₂ : Ixs → Ixs → TyCon} 
                          → (monad₁ : Monad M₁) → (monad₂ : IxMonad Ixs M₂) 
                          → PrincipalPM (polymonadCompose (Monad→ComposablePolymonad monad₁) (IxMonad→ComposablePolymonad monad₂))
principalPolymonadMonadIxMonadCompose {Ixs = Ixs} monad₁ monad₂ = princ
  where
    
    TyCons = IdTyCons ⊎ (MonadTyCons ⊎ IxMonadTyCons Ixs)
    
    cpm₁ = Monad→ComposablePolymonad monad₁
    cpm₂ = IxMonad→ComposablePolymonad monad₂

    pm₁ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₁ = cpmPolymonad cpm₁

    pm₂ : Polymonad (IdTyCons ⊎ IxMonadTyCons Ixs) idTC
    pm₂ = cpmPolymonad cpm₂
    
    pm : Polymonad TyCons idTC
    pm = polymonadCompose cpm₁ cpm₂

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
