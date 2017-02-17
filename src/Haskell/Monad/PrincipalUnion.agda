 
module Haskell.Monad.PrincipalUnion where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit hiding ( _≟_ )
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.Core using ( Decidable )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad.Definition
open import Polymonad.Unionable
open import Polymonad.Principal
open import Polymonad.Union
open import Haskell.Parameterized.IndexedMonad
open import Haskell.Parameterized.IndexedMonad.Polymonad
open import Haskell.Parameterized.IndexedMonad.Unionable
open import Haskell.Monad
open import Haskell.Monad.Polymonad
open import Haskell.Monad.Unionable

-- -----------------------------------------------------------------------------
-- EXAMPLE for principality of polymonad union
-- Union of two standard monads is principal
-- -----------------------------------------------------------------------------

principalMonadUnion : ∀ {M₁ M₂ : TyCon} 
                          → (monad₁ : Monad M₁) → (monad₂ : Monad M₂)
                          → ( (x : ((IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)) × (IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)))) 
                            → (F : SubsetOf ((IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)) × (IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)))) 
                            → Dec (x ∈ F))
                          → PrincipalPM (polymonadUnion (Monad→UnionablePolymonad monad₁) (Monad→UnionablePolymonad monad₂))
principalMonadUnion monad₁ monad₂ _∈?_ = princ
  where
    TyCons = IdTyCons ⊎ (MonadTyCons ⊎ MonadTyCons)
    
    upm₁ = Monad→UnionablePolymonad monad₁
    upm₂ = Monad→UnionablePolymonad monad₂

    pm₁ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₁ = upmPolymonad upm₁

    pm₂ : Polymonad (IdTyCons ⊎ MonadTyCons) idTC
    pm₂ = upmPolymonad upm₂
    
    pm : Polymonad TyCons idTC
    pm = polymonadUnion upm₁ upm₂

    mTC₁ : TyCons
    mTC₁ = inj₂ (inj₁ MonadTC)
    
    mTC₂ : TyCons
    mTC₂ = inj₂ (inj₂ MonadTC)
    
    contradiction : ∀ {l} {P : Set l} → P → ¬ P → ⊥
    contradiction P ¬P = ¬P P

    mixedPrinc : (F : SubsetOf (TyCons × TyCons)) 
                   → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ inj₂ (inj₁ MonadTC))
                   → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ inj₂ (inj₂ MonadTC))
                   → Dec ((mTC₁ , idTC) ∈ F)
                   → Dec ((idTC , mTC₁) ∈ F)
                   → Dec ((mTC₂ , idTC) ∈ F)
                   → Dec ((idTC , mTC₂) ∈ F)
                   → Dec ((mTC₁ , mTC₂) ∈ F)
                   → Dec ((mTC₂ , mTC₁) ∈ F)
                   → Dec ((mTC₁ , mTC₁) ∈ F)
                   → Dec ((mTC₂ , mTC₂) ∈ F)
                   → ∃ (λ M̂ → B[ M̂ , idTC ] pm ▷ inj₂ (inj₁ MonadTC)
                            × B[ M̂ , idTC ] pm ▷ inj₂ (inj₂ MonadTC)
                            × ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
    mixedPrinc F morph₁ morph₂ (yes M₁I∈F) IM₁∈?F M₂I∈?F IM₂∈?F M₁M₂∈?F M₂M₁∈?F M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₂ mTC₁ idTC M₁I∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (yes IM₁∈F) M₂I∈?F IM₂∈?F M₁M₂∈?F M₂M₁∈?F M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₂ idTC mTC₁ IM₁∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (yes M₂I∈F) IM₂∈?F M₁M₂∈?F M₂M₁∈?F M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₁ mTC₂ idTC M₂I∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (yes IM₂∈F) M₁M₂∈?F M₂M₁∈?F M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₁ idTC mTC₂ IM₂∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (no ¬IM₂∈F) (yes M₁M₂∈F) M₂M₁∈?F M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₂ mTC₁ mTC₂ M₁M₂∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (no ¬IM₂∈F) (no ¬M₁M₂∈F) (yes M₂M₁∈F) M₁M₁∈?F M₂M₂∈?F = ⊥-elim (morph₁ mTC₂ mTC₁ M₂M₁∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (no ¬IM₂∈F) (no ¬M₁M₂∈F) (no ¬M₂M₁∈F) (yes M₁M₁∈F) M₂M₂∈?F = ⊥-elim (morph₂ mTC₁ mTC₁ M₁M₁∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (no ¬IM₂∈F) (no ¬M₁M₂∈F) (no ¬M₂M₁∈F) (no ¬M₁M₁∈F) (yes M₂M₂∈F) = ⊥-elim (morph₁ mTC₂ mTC₂ M₂M₂∈F)
    mixedPrinc F morph₁ morph₂ (no ¬M₁I∈F) (no ¬IM₁∈F) (no ¬M₂I∈F) (no ¬IM₂∈F) (no ¬M₁M₂∈F) (no ¬M₂M₁∈F) (no ¬M₁M₁∈F) (no ¬M₂M₂∈F) = solution
      where
        newMorph : (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ idTC
        newMorph (inj₁ IdentTC) (inj₁ IdentTC) II∈F = IdentB
        newMorph (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) IM₁∈F = ⊥-elim (contradiction IM₁∈F ¬IM₁∈F)
        newMorph (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) IM₂∈F = ⊥-elim (contradiction IM₂∈F ¬IM₂∈F)
        newMorph (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) M₁I∈F = ⊥-elim (contradiction M₁I∈F ¬M₁I∈F)
        newMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) M₁M₁∈F = ⊥-elim (contradiction M₁M₁∈F ¬M₁M₁∈F)
        newMorph (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) M₁M₂∈F = ⊥-elim (contradiction M₁M₂∈F ¬M₁M₂∈F)
        newMorph (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) M₂I∈F = ⊥-elim (contradiction M₂I∈F ¬M₂I∈F)
        newMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) M₂M₁∈F = ⊥-elim (contradiction M₂M₁∈F ¬M₂M₁∈F)
        newMorph (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) M₂M₂∈F = ⊥-elim (contradiction M₂M₂∈F ¬M₂M₂∈F)
        
        solution : ∃ (λ M̂ → B[ M̂ , idTC ] pm ▷ inj₂ (inj₁ MonadTC) 
                          × B[ M̂ , idTC ] pm ▷ inj₂ (inj₂ MonadTC) 
                          × ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
        solution = idTC , ReturnB , ReturnB , newMorph

    princ : PrincipalPM pm
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ = idTC , IdentB , IdentB , morph₁
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = idTC , IdentB , ReturnB , morph₁
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) morph₁ morph₂ = idTC , IdentB , ReturnB , morph₁
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) morph₁ morph₂ = idTC , ReturnB , IdentB , morph₂
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = mTC₁ , FunctorB , FunctorB , morph₁
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) morph₁ morph₂ = 
      mixedPrinc F morph₁ morph₂ 
        ((mTC₁ , idTC) ∈? F) ((idTC , mTC₁) ∈? F) 
        ((mTC₂ , idTC) ∈? F) ((idTC , mTC₂) ∈? F)
        ((mTC₁ , mTC₂) ∈? F) ((mTC₂ , mTC₁) ∈? F)
        ((mTC₁ , mTC₁) ∈? F) ((mTC₂ , mTC₂) ∈? F)
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) morph₁ morph₂ = idTC , ReturnB , IdentB , morph₂
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) morph₁ morph₂ = 
      let M , b₁ , b₂ , morph = mixedPrinc F morph₂ morph₁ 
                                  ((mTC₁ , idTC) ∈? F) ((idTC , mTC₁) ∈? F) 
                                  ((mTC₂ , idTC) ∈? F) ((idTC , mTC₂) ∈? F)
                                  ((mTC₁ , mTC₂) ∈? F) ((mTC₂ , mTC₁) ∈? F)
                                  ((mTC₁ , mTC₁) ∈? F) ((mTC₂ , mTC₂) ∈? F)
      in M , b₂ , b₁ , morph
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) morph₁ morph₂ = mTC₂ , FunctorB , FunctorB , morph₂
