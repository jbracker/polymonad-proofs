 
module Polymonad.Union.Principal where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit hiding ( _≟_ )
open import Data.Empty
open import Data.Bool
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
open import Polymonad.Union.Unionable
open import Polymonad.Union.Properties
open import Polymonad.Union.Principal.Utilities
open import Haskell.Monad.Polymonad
open import Haskell.Monad.Unionable
open import Haskell.Monad.List
open import Haskell.Monad.Maybe

principalPolymonadUnion : ∀ {TyCons₁ TyCons₂ : Set}
                        → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
                        → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
                        → (upm₁ : UnionablePolymonad pm₁)
                        → (upm₂ : UnionablePolymonad pm₂)
                        -- We know that F falls in either of three categories:
                        --  - F is a subset of (IdTyCons ⊎ TyCons₁)²
                        --  - F is a subset of (IdTyCons ⊎ TyCons₂)²
                        --  - F contains a pair with a tycon from TyCons₁ and a pair with a tycon from TyCons₂ (could be the same pair).
                        → ( (F : SubsetOf ((IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) × (IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)))) 
                         → ( ∀ (M M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) 
                            → (M , M') ∈ F 
                            → ∃ λ(M₁ : IdTyCons ⊎ TyCons₁) → ∃ λ(M₁' : IdTyCons ⊎ TyCons₁) 
                            → (M ≡ mTyCon₁ M₁) × (M' ≡ mTyCon₁ M₁') )
                          ⊎ ( ∀ (M M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) 
                            → (M , M') ∈ F 
                            → ∃ λ(M₂ : IdTyCons ⊎ TyCons₂) → ∃ λ(M₂' : IdTyCons ⊎ TyCons₂) 
                            → (M ≡ mTyCon₂ M₂) × (M' ≡ mTyCon₂ M₂') )
                          ⊎ ( ∃ λ(M₁ : TyCons₁) → ∃ λ(M₂ : TyCons₂) 
                            → ∃ λ(M : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → ∃ λ(M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) 
                            → ( (inj₂ (inj₁ M₁) , M) ∈ F ⊎ (M , inj₂ (inj₁ M₁)) ∈ F) × ( (inj₂ (inj₂ M₂) , M') ∈ F ⊎ (M' , inj₂ (inj₂ M₂)) ∈ F )  ) )
                        -- We know if either:
                        --  - F one element that is not (Id,Id)
                        --  - F = { (Id,Id) }
                        --  - F = ∅
                        → ( (F : SubsetOf ((IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) × (IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)))) 
                          → ( (∃ λ(M : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → ∃ λ(M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → (M , M') ∈ F × (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)))
                            ⊎ ( ((idTC , idTC) ∈ F × (∀ (M M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)) → ¬ ((M , M') ∈ F)))
                            ⊎ (∀ (M M' : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → ¬ (M , M') ∈ F) ) )
                          )
                        → PrincipalPM pm₁
                        → PrincipalPM pm₂
                        → PrincipalPM (polymonadUnion upm₁ upm₂)
principalPolymonadUnion {TyCons₁} {TyCons₂} {pm₁} {pm₂} upm₁ upm₂ partition onlyIdPair princ₁ princ₂ = princ
  where
    open Polymonad

    pm = polymonadUnion upm₁ upm₂
    upm = polymonadUnionableUnion upm₁ upm₂
    
    TyCons = IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)

    idMorph¬∃ = upmIdMorph¬∃ upm

    mTC₁ : TyCons₁ → TyCons
    mTC₁ M = inj₂ (inj₁ M)

    mTC₂ : TyCons₂ → TyCons
    mTC₂ M = inj₂ (inj₂ M)

    morphId : (F : SubsetOf (TyCons × TyCons))
            → (∀ (M M' : TyCons) → (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)) → ¬ ((M , M') ∈ F))
            → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ idTC )
    morphId F F≡IdId (inj₁ IdentTC) (inj₁ IdentTC) NN∈F = lawFunctor1 pm₁ (inj₁ IdentTC)
    morphId F F≡IdId (inj₁ IdentTC) (inj₂ (inj₁ N')) NN∈F = ⊥-elim (F≡IdId idTC (mTC₁ N') (inj₂ (λ ())) NN∈F)
    morphId F F≡IdId (inj₁ IdentTC) (inj₂ (inj₂ N')) NN∈F = ⊥-elim (F≡IdId idTC (mTC₂ N') (inj₂ (λ ())) NN∈F)
    morphId F F≡IdId (inj₂ N) N' NN∈F = ⊥-elim (F≡IdId (inj₂ N) N' (inj₁ (λ ())) NN∈F)
    
    helpPrinc1 : (F : SubsetOf ( TyCons × TyCons ))
               → (M₁ : TyCons₁) → (M₂ : TyCons)
               -- All pairs in F are from (IdTyCons ⊎ TyCons₁)²
               → ( ∀ (M M' : TyCons) → (M , M') ∈ F 
                 → ∃ λ(M₂ : IdTyCons ⊎ TyCons₂) → ∃ λ(M₂' : IdTyCons ⊎ TyCons₂) 
                 → (M ≡ mTyCon₂ M₂) × (M' ≡ mTyCon₂ M₂') )
               -- Create binds to TyCons₁
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ mTC₁ M₁ )
               -- Create binds to TyCons₂
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M₂ )
               -- F contains for then just identity
               → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F × (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)))
               -- Principality result pair
               → ( ∃ λ(M̂ : TyCons) → B[ M̂ , idTC ] pm ▷ mTC₁ M₁ × B[ M̂ , idTC ] pm ▷ M₂ 
                 × ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M̂ ) )
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (¬N≡Id refl)
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id)
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₁ N') , NN∈F , inj₂ ¬N'≡Id)
      = ⊥-elim (pairIn2→⊥ F pairIn2 idTC (mTC₁ N') NN∈F (N' , inj₂ refl))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₂ N') , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = idTC} {M₂ = N'} {M₁ = M₁} (morph₁ idTC (mTC₂ N') NN∈F))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) idTC NN∈F (N , inj₁ refl))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = idTC} {M₁ = M₁} (morph₁ (mTC₂ N) idTC NN∈F))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) (mTC₁ N') NN∈F (N , inj₁ refl))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id)
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = mTC₁ N} {M₂ = N'} {M₁ = M₁} (morph₁ (mTC₁ N) (mTC₂ N') NN∈F))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = mTC₁ N'} {M₁ = M₁} (morph₁ (mTC₂ N) (mTC₁ N') NN∈F))
    helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = mTC₂ N'} {M₁ = M₁} (morph₁ (mTC₂ N) (mTC₂ N') NN∈F))
    
    helpPrinc2 : (F : SubsetOf ( TyCons × TyCons ))
               → (M₁ : TyCons) → (M₂ : TyCons₁)
               -- All pairs in F are from (IdTyCons ⊎ TyCons₁)²
               → ( ∀ (M M' : TyCons) → (M , M') ∈ F 
                 → ∃ λ(M₂ : IdTyCons ⊎ TyCons₂) → ∃ λ(M₂' : IdTyCons ⊎ TyCons₂) 
                 → (M ≡ mTyCon₂ M₂) × (M' ≡ mTyCon₂ M₂') )
               -- Create binds to TyCons₁
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M₁ )
               -- Create binds to TyCons₂
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ mTC₁ M₂ )
               -- F contains for then just identity
               → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F × (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)))
               -- Principality result pair
               → ( ∃ λ(M̂ : TyCons) → B[ M̂ , idTC ] pm ▷ M₁ × B[ M̂ , idTC ] pm ▷ mTC₁ M₂ 
                 × ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M̂ ) )
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (¬N≡Id refl)
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₁ N') , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (pairIn2→⊥ F pairIn2 idTC (mTC₁ N') NN∈F (N' , inj₂ refl))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₂ N') , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = idTC} {M₂ = N'} {M₁ = M₂} (morph₂ idTC (mTC₂ N') NN∈F))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) idTC NN∈F (N , inj₁ refl))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = idTC} {M₁ = M₂} (morph₂ (mTC₂ N) idTC NN∈F))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) (mTC₁ N') NN∈F (N , inj₁ refl))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id)
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = mTC₁ N} {M₂ = N'} {M₁ = M₂} (morph₂ (mTC₁ N) (mTC₂ N') NN∈F))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = mTC₁ N'} {M₁ = M₂} (morph₂ (mTC₂ N) (mTC₁ N') NN∈F))
    helpPrinc2 F M₁ M₂ pairIn2 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N} {N = mTC₂ N'} {M₁ = M₂} (morph₂ (mTC₂ N) (mTC₂ N') NN∈F))

    helpPrinc3 : (F : SubsetOf ( TyCons × TyCons ))
                → (M₁ : TyCons₂) → (M₂ : TyCons)
                -- All pairs in F are from (IdTyCons ⊎ TyCons₁)²
                → ( ∀ (M M' : TyCons) → (M , M') ∈ F 
                  → ∃ λ(M₁ : IdTyCons ⊎ TyCons₁) → ∃ λ(M₁' : IdTyCons ⊎ TyCons₁) 
                  → (M ≡ mTyCon₁ M₁) × (M' ≡ mTyCon₁ M₁') )
                -- Create binds to M₁
                → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ mTC₂ M₁ )
                -- Create binds to M₂
                → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M₂ )
                -- F contains for then just identity
                → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F × (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)))
                -- Principality result pair
                → ( ∃ λ(M̂ : TyCons) → B[ M̂ , idTC ] pm ▷ mTC₂ M₁ × B[ M̂ , idTC ] pm ▷ M₂
                  × ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M̂ ) )
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (¬N≡Id refl)
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₁ N') , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = idTC} {M₁ = N'} {M₂ = M₁} (morph₁ idTC (mTC₁ N') NN∈F))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₂ N') , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 idTC (mTC₂ N') NN∈F (N' , (inj₂ refl)))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id)
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = idTC} {M₂ = M₁} (morph₁ (mTC₁ N) idTC NN∈F))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) idTC NN∈F (N , (inj₁ refl)))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = mTC₁ N'} {M₂ = M₁} (morph₁ (mTC₁ N) (mTC₁ N') NN∈F))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id)
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = mTC₂ N'} {M₂ = M₁} (morph₁ (mTC₁ N) (mTC₂ N') NN∈F))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = mTC₂ N} {M₁ = N'} {M₂ = M₁} (morph₁ (mTC₂ N) (mTC₁ N') NN∈F))
    helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) (mTC₂ N') NN∈F (N , (inj₁ refl)))
    
    helpPrinc4 : (F : SubsetOf ( TyCons × TyCons ))
               → (M₁ : TyCons) → (M₂ : TyCons₂)
               -- All pairs in F are from (IdTyCons ⊎ TyCons₁)²
               → ( ∀ (M M' : TyCons) → (M , M') ∈ F 
                 → ∃ λ(M₁ : IdTyCons ⊎ TyCons₁) → ∃ λ(M₁' : IdTyCons ⊎ TyCons₁) 
                 → (M ≡ mTyCon₁ M₁) × (M' ≡ mTyCon₁ M₁') )
               -- Create binds to TyCons₁
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M₁ )
               -- Create binds to TyCons₂
               → ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ mTC₂ M₂ )
               -- F contains for then just identity
               → (∃ λ(M : TyCons) → ∃ λ(M' : TyCons) → (M , M') ∈ F × (¬ (M ≡ idTC) ⊎ ¬ (M' ≡ idTC)))
               -- Principality result pair
               → ( ∃ λ(M̂ : TyCons) → B[ M̂ , idTC ] pm ▷ M₁ × B[ M̂ , idTC ] pm ▷ mTC₂ M₂ 
                 × ( (N N' : TyCons) → (N , N') ∈ F → B[ N , N' ] pm ▷ M̂ ) )
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (¬N≡Id refl)
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₁ N) , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = idTC} {M₁ = N} {M₂ = M₂} (morph₂ idTC (mTC₁ N) NN∈F))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₁ IdentTC , inj₂ (inj₂ N) , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 idTC (mTC₂ N) NN∈F (N , inj₂ refl))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = idTC} {M₂ = M₂} (morph₂ (mTC₁ N) idTC NN∈F))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) idTC NN∈F (N , inj₁ refl))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      = ⊥-elim (¬N'≡Id refl)
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = mTC₁ N'} {M₂ = M₂} (morph₂ (mTC₁ N) (mTC₁ N') NN∈F))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₁ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id)
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N} {N = mTC₂ N'} {M₂ = M₂} (morph₂ (mTC₁ N) (mTC₂ N') NN∈F))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = mTC₂ N} {M₁ = N'} {M₂ = M₂} (morph₂ (mTC₂ N) (mTC₁ N') NN∈F))
    helpPrinc4 F M₁ M₂ pairIn1 morph₁ morph₂ (inj₂ (inj₂ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) (mTC₂ N') NN∈F (N , inj₁ refl))
    
    princ : PrincipalPM pm
    princ F (M , M' , MM'∈F) M₁ M₂ morph₁ morph₂ with onlyIdPair F
    princ F (M , M' , MM'∈F) M₁ M₂ morph₁ morph₂ | inj₁ FmoreThenId with partition F
    
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      | inj₁ pairIn1 = ⊥-elim (¬N≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) | inj₁ pairIn1 
      = ⊥-elim (¬N'≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₂ (inj₁ N') , NN∈F , inj₂ ¬N'≡Id) | inj₁ pairIn1 
      = ⊥-elim (idMorph¬∃ {M = idTC} {N = mTC₁ N'} (inj₂ (inj₁ N' , refl)) (morph₁ idTC (mTC₁ N') NN∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₂ (inj₂ N') , NN∈F , inj₂ ¬N'≡Id) | inj₁ pairIn1 
      = ⊥-elim (pairIn1→⊥ F pairIn1 idTC (mTC₂ N') NN∈F (N' , (inj₂ refl)))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) | inj₁ pairIn1 
      = ⊥-elim (idMorph¬∃ {M = mTC₁ N} {N = idTC} (inj₁ (inj₁ N , refl)) (morph₁ (mTC₁ N) idTC NN∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) | inj₁ pairIn1 
      = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) idTC NN∈F (N , (inj₁ refl)))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      | inj₁ pairIn1 = ⊥-elim (¬N'≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₁ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      | inj₁ pairIn1 = ⊥-elim (idMorph¬∃ {M = mTC₁ N} {N = mTC₁ N'} (inj₁ (inj₁ N , refl)) (morph₁ (mTC₁ N) (mTC₁ N') NN∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₁ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      | inj₁ pairIn1 = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₁ N) (mTC₂ N') NN∈F (N' , (inj₂ refl)))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₂ N) , inj₂ N' , NN∈F , ¬N≡Id) 
      | inj₁ pairIn1 = ⊥-elim (pairIn1→⊥ F pairIn1 (mTC₂ N) (inj₂ N') NN∈F (N , (inj₁ refl)))
    
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₁ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1 
      = princ₁→princ upm₁ upm₂ F pairIn1 idTC (inj₂ M₂) 
                     (princ₁ (F→F₁ F) (NN∈F→NN∈F₁ F pairIn1 M M' MM'∈F) idTC (inj₂ M₂) 
                             (morph→morph₁ upm₁ upm₂ F idTC morph₁) 
                             (morph→morph₁ upm₁ upm₂ F (inj₂ M₂) morph₂))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₂ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1 
      = helpPrinc4 F idTC M₂ pairIn1 morph₁ morph₂ FmoreThenId
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) (inj₁ IdentTC) morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1 
      = princ₁→princ upm₁ upm₂ F pairIn1 (inj₂ M₁) idTC 
                     (princ₁ (F→F₁ F) (NN∈F→NN∈F₁ F pairIn1 M M' MM'∈F) (inj₂ M₁) idTC 
                             (morph→morph₁ upm₁ upm₂ F (inj₂ M₁) morph₁) 
                             (morph→morph₁ upm₁ upm₂ F idTC morph₂))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) (inj₂ (inj₁ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1 
      = princ₁→princ upm₁ upm₂ F pairIn1 (inj₂ M₁) (inj₂ M₂) 
                     (princ₁ (F→F₁ F) (NN∈F→NN∈F₁ F pairIn1 M M' MM'∈F) (inj₂ M₁) (inj₂ M₂) 
                             (morph→morph₁ upm₁ upm₂ F (inj₂ M₁) morph₁) 
                             (morph→morph₁ upm₁ upm₂ F (inj₂ M₂) morph₂))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) (inj₂ (inj₂ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1
      = helpPrinc4 F (mTC₁ M₁) M₂ pairIn1 morph₁ morph₂ FmoreThenId
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₁ pairIn1 
      = helpPrinc3 F M₁ M₂ pairIn1 morph₁ morph₂ FmoreThenId
    
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , N' , NN∈F , inj₁ ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (¬N≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (¬N'≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₂ (inj₁ N') , NN∈F , inj₂ ¬N'≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (pairIn2→⊥ F pairIn2 idTC (mTC₁ N') NN∈F (N' , inj₂ refl))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₁ IdentTC , inj₂ (inj₂ N') , NN∈F , inj₂ ¬N'≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (idMorph¬∃ {M = idTC} {N = mTC₂ N'} (inj₂ (inj₂ N' , refl)) (morph₁ idTC (mTC₂ N') NN∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₁ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) idTC NN∈F (N , inj₁ refl))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₂ N) , inj₁ IdentTC , NN∈F , inj₁ ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (idMorph¬∃ {M = mTC₂ N} {N = idTC} (inj₁ (inj₂ N , refl)) (morph₁ (mTC₂ N) idTC NN∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ N , inj₁ IdentTC , NN∈F , inj₂ ¬N'≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (¬N'≡Id refl)
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₁ N) , inj₂ N' , NN∈F , ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₁ N) (inj₂ N') NN∈F (N , inj₁ refl))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₂ N) , inj₂ (inj₁ N') , NN∈F , ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (pairIn2→⊥ F pairIn2 (mTC₂ N) (mTC₁ N') NN∈F (N' , inj₂ refl))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₁ IdentTC) morph₁ morph₂ | inj₁ (inj₂ (inj₂ N) , inj₂ (inj₂ N') , NN∈F , ¬N≡Id) 
      | inj₂ (inj₁ pairIn2) = ⊥-elim (idMorph¬∃ {M = mTC₂ N} {N = mTC₂ N'} (inj₁ (inj₂ N , refl)) (morph₁ (mTC₂ N) (mTC₂ N') NN∈F))
    
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₁ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = helpPrinc2 F idTC M₂ pairIn2 morph₁ morph₂ FmoreThenId
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) (inj₂ (inj₂ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = princ₂→princ upm₁ upm₂ F pairIn2 idTC (inj₂ M₂)  
                     (princ₂ (F→F₂ F) (NN∈F→NN∈F₂ F pairIn2 M M' MM'∈F) idTC (inj₂ M₂) 
                             (morph→morph₂ upm₁ upm₂ F idTC morph₁)
                             (morph→morph₂ upm₁ upm₂ F (inj₂ M₂) morph₂))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) M₂   morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = helpPrinc1 F M₁ M₂ pairIn2 morph₁ morph₂ FmoreThenId
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) (inj₁ IdentTC)   morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = princ₂→princ upm₁ upm₂ F pairIn2 (inj₂ M₁) idTC 
                     (princ₂ (F→F₂ F) (NN∈F→NN∈F₂ F pairIn2 M M' MM'∈F) (inj₂ M₁) idTC 
                             (morph→morph₂ upm₁ upm₂ F (inj₂ M₁) morph₁) 
                             (morph→morph₂ upm₁ upm₂ F idTC morph₂))
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) (inj₂ (inj₁ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = helpPrinc2 F (mTC₂ M₁) M₂ pairIn2 morph₁ morph₂ FmoreThenId
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) (inj₂ (inj₂ M₂)) morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₁ pairIn2) 
      = princ₂→princ upm₁ upm₂ F pairIn2 (inj₂ M₁) (inj₂ M₂) 
                     (princ₂ (F→F₂ F) (NN∈F→NN∈F₂ F pairIn2 M M' MM'∈F) (inj₂ M₁) (inj₂ M₂) 
                             (morph→morph₂ upm₁ upm₂ F (inj₂ M₁) morph₁) 
                             (morph→morph₂ upm₁ upm₂ F (inj₂ M₂) morph₂))
    
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₁ N₂N'∈F))
      = ⊥-elim (idMorph¬∃ {M = mTC₁ N₁} {N = N} (inj₁ ((inj₁ N₁) , refl)) (morph₁ (mTC₁ N₁) N N₁N∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₁ N₂N'∈F)) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N₂} {N = N'} {M₁ = M₁} (morph₁ (mTC₂ N₂) N' N₂N'∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₁ N₂N'∈F)) 
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N₁} {N = N} {M₂ = M₁} (morph₁ (mTC₁ N₁) N N₁N∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₂ N'N₂∈F)) 
      = ⊥-elim (idMorph¬∃ {M = mTC₁ N₁} {N = N} (inj₁ ((inj₁ N₁) , refl)) (morph₁ (mTC₁ N₁) N N₁N∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₂ N'N₂∈F)) 
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = N'} {M₂ = N₂} {M₁ = M₁} (morph₁ N' (mTC₂ N₂) N'N₂∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₁ N₁N∈F , inj₂ N'N₂∈F)) 
      = ⊥-elim (union→¬[M₁,N]▷M₂ upm {M₁ = N₁} {N = N} {M₂ = M₁} (morph₁ (mTC₁ N₁) N N₁N∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₁ N₂N'∈F)) 
      = ⊥-elim (idMorph¬∃ {M = N} {N = mTC₁ N₁} (inj₂ ((inj₁ N₁) , refl)) (morph₁ N (mTC₁ N₁) NN₁∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₁ N₂N'∈F)) 
      = ⊥-elim (union→¬[M₂,N]▷M₁ upm {M₂ = N₂} {N = N'} {M₁ = M₁} (morph₁ (mTC₂ N₂) N' N₂N'∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₁ N₂N'∈F)) 
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = N} {M₁ = N₁} {M₂ = M₁} (morph₁ N (mTC₁ N₁) NN₁∈F))
    princ F (M , M' , MM'∈F) (inj₁ IdentTC) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₂ N'N₂∈F)) 
      = ⊥-elim (idMorph¬∃ {M = N} {N = mTC₁ N₁} (inj₂ ((inj₁ N₁) , refl)) (morph₁ N (mTC₁ N₁) NN₁∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₁ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₂ N'N₂∈F)) 
      = ⊥-elim (union→¬[N,M₂]▷M₁ upm {N = N'} {M₂ = N₂} {M₁ = M₁} (morph₁ N' (mTC₂ N₂) N'N₂∈F))
    princ F (M , M' , MM'∈F) (inj₂ (inj₂ M₁)) M₂ morph₁ morph₂ | inj₁ FmoreThenId | inj₂ (inj₂ (N₁ , N₂ , N , N' , inj₂ NN₁∈F , inj₂ N'N₂∈F))
      = ⊥-elim (union→¬[N,M₁]▷M₂ upm {N = N} {M₁ = N₁} {M₂ = M₁} (morph₁ N (mTC₁ N₁) NN₁∈F))
    princ F (M , M' , MM'∈F) M₁ M₂ morph₁ morph₂ | inj₂ (inj₁ (IdId∈F , F≡IdId)) 
      = idTC , morph₁ idTC idTC IdId∈F , morph₂ idTC idTC IdId∈F , morphId F F≡IdId
    princ F (M , M' , MM'∈F) M₁ M₂ morph₁ morph₂ | inj₂ (inj₂ Fempty) = ⊥-elim (Fempty M M' MM'∈F) 

