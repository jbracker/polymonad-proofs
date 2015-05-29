 
module Polymonad.PrincipalComposition where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit hiding ( _≟_ )
open import Data.Empty
open import Data.Bool
open import Relation.Nullary.Core
open import Relation.Binary.Core using ( Decidable )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Haskell
open import Identity
open import Polymonad
open import Polymonad.Composable
open import Polymonad.Principal
open import Polymonad.Composition
open import Monad.Polymonad
open import Monad.Composable
open import Monad.List
open import Monad.Maybe

principalPolymonadCompose : ∀ {TyCons₁ TyCons₂ : Set}
                          → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
                          → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
                          → (cpm₁ : ComposablePolymonad pm₁)
                          → (cpm₂ : ComposablePolymonad pm₂)
                          → PrincipalPM pm₁
                          → PrincipalPM pm₂
                          → (∀ (M N P : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)) → B[ M , N ] (polymonadCompose cpm₁ cpm₂) ▷ P ⊎ ¬ (B[ M , N ] (polymonadCompose cpm₁ cpm₂) ▷ P))
                          → PrincipalPM (polymonadCompose cpm₁ cpm₂)
principalPolymonadCompose {TyCons₁} {TyCons₂} {pm₁} {pm₂} cpm₁ cpm₂ princ₁ princ₂ noneOrSomeBind = princ
  where
    open Polymonad.Polymonad

    pm = polymonadCompose cpm₁ cpm₂
    TyCons = IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)

    idMorph¬∃₁ = cpmIdMorph¬∃ cpm₁
    
    TC₁→TC : IdTyCons ⊎ TyCons₁ → TyCons
    TC₁→TC (inj₁ IdentTC) = inj₁ IdentTC
    TC₁→TC (inj₂ M) = inj₂ (inj₁ M)
    
    TC₂→TC : IdTyCons ⊎ TyCons₂ → TyCons
    TC₂→TC (inj₁ IdentTC) = inj₁ IdentTC
    TC₂→TC (inj₂ M) = inj₂ (inj₂ M)
    
    B[M₁N₂]▷P≡⊥ : (M : TyCons₁) → (N : TyCons₂) → (P : TyCons) → B[ TC₁→TC (inj₂ M) , TC₂→TC (inj₂ N) ] pm ▷ P ≡ ⊥
    B[M₁N₂]▷P≡⊥ M₁ N₂ (inj₁ IdentTC) = refl
    B[M₁N₂]▷P≡⊥ M₁ N₂ (inj₂ (inj₁ P₁)) = refl
    B[M₁N₂]▷P≡⊥ M₁ N₂ (inj₂ (inj₂ P₂)) = refl
    
    B[M₂N₁]▷P≡⊥ : (M : TyCons₂) → (N : TyCons₁) → (P : TyCons) → B[ TC₂→TC (inj₂ M) , TC₁→TC (inj₂ N) ] pm ▷ P ≡ ⊥
    B[M₂N₁]▷P≡⊥ M₂ N₁ (inj₁ IdentTC) = refl
    B[M₂N₁]▷P≡⊥ M₂ N₁ (inj₂ (inj₁ P₁)) = refl
    B[M₂N₁]▷P≡⊥ M₂ N₁ (inj₂ (inj₂ P₂)) = refl
    
    eqBindT₁ : (M N P : IdTyCons ⊎ TyCons₁) → B[ M , N ] pm₁ ▷ P ≡ B[ TC₁→TC M , TC₁→TC N ] pm ▷ TC₁→TC P
    eqBindT₁ (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) = refl
    eqBindT₁ (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P      ) = refl
    eqBindT₁ (inj₁ IdentTC) (inj₂ N      ) (inj₁ IdentTC) = refl
    eqBindT₁ (inj₁ IdentTC) (inj₂ N      ) (inj₂ P      ) = refl
    eqBindT₁ (inj₂ M      ) (inj₁ IdentTC) (inj₁ IdentTC) = refl
    eqBindT₁ (inj₂ M      ) (inj₁ IdentTC) (inj₂ P      ) = refl
    eqBindT₁ (inj₂ M      ) (inj₂ N      ) (inj₁ IdentTC) = refl
    eqBindT₁ (inj₂ M      ) (inj₂ N      ) (inj₂ P      ) = refl
    
    eqBindT₂ : (M N P : IdTyCons ⊎ TyCons₂) → B[ M , N ] pm₂ ▷ P ≡ B[ TC₂→TC M , TC₂→TC N ] pm ▷ TC₂→TC P
    eqBindT₂ (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) = trans (cpmLawEqIdBinds cpm₂) (sym (cpmLawEqIdBinds cpm₁))
    eqBindT₂ (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ P      ) = refl
    eqBindT₂ (inj₁ IdentTC) (inj₂ N      ) (inj₁ IdentTC) = refl
    eqBindT₂ (inj₁ IdentTC) (inj₂ N      ) (inj₂ P      ) = refl
    eqBindT₂ (inj₂ M      ) (inj₁ IdentTC) (inj₁ IdentTC) = refl
    eqBindT₂ (inj₂ M      ) (inj₁ IdentTC) (inj₂ P      ) = refl
    eqBindT₂ (inj₂ M      ) (inj₂ N      ) (inj₁ IdentTC) = refl
    eqBindT₂ (inj₂ M      ) (inj₂ N      ) (inj₂ P      ) = refl
    
    F₁→F : SubsetOf ((IdTyCons ⊎ TyCons₁) × (IdTyCons ⊎ TyCons₁))
         → SubsetOf (TyCons × TyCons)
    F₁→F F₁ (inj₁ IdentTC   , inj₁ IdentTC   ) = F₁ (idTC , idTC)
    F₁→F F₁ (inj₁ IdentTC   , inj₂ (inj₁ M₁')) = F₁ (idTC , inj₂ M₁')
    F₁→F F₁ (inj₁ IdentTC   , inj₂ (inj₂ M₂')) = false
    F₁→F F₁ (inj₂ (inj₁ M₁) , inj₁ IdentTC   ) = F₁ (inj₂ M₁ , idTC)
    F₁→F F₁ (inj₂ (inj₁ M₁) , inj₂ (inj₁ M₁')) = F₁ (inj₂ M₁ , inj₂ M₁')
    F₁→F F₁ (inj₂ (inj₁ M₁) , inj₂ (inj₂ M₂')) = false
    F₁→F F₁ (inj₂ (inj₂ M₂) , inj₁ IdentTC   ) = false
    F₁→F F₁ (inj₂ (inj₂ M₂) , inj₂ (inj₁ M₁')) = false
    F₁→F F₁ (inj₂ (inj₂ M₂) , inj₂ (inj₂ M₂')) = false

    F₂→F : SubsetOf ((IdTyCons ⊎ TyCons₂) × (IdTyCons ⊎ TyCons₂))
         → SubsetOf (TyCons × TyCons)
    F₂→F F₂ (inj₁ IdentTC   , inj₁ IdentTC   ) = F₂ (idTC , idTC)
    F₂→F F₂ (inj₁ IdentTC   , inj₂ (inj₁ M₁')) = false
    F₂→F F₂ (inj₁ IdentTC   , inj₂ (inj₂ M₂')) = F₂ (idTC , inj₂ M₂')
    F₂→F F₂ (inj₂ (inj₁ M₁) , inj₁ IdentTC   ) = false
    F₂→F F₂ (inj₂ (inj₁ M₁) , inj₂ (inj₁ M₁')) = false
    F₂→F F₂ (inj₂ (inj₁ M₁) , inj₂ (inj₂ M₂')) = false
    F₂→F F₂ (inj₂ (inj₂ M₂) , inj₁ IdentTC   ) = F₂ (inj₂ M₂ , idTC)
    F₂→F F₂ (inj₂ (inj₂ M₂) , inj₂ (inj₁ M₁')) = false
    F₂→F F₂ (inj₂ (inj₂ M₂) , inj₂ (inj₂ M₂')) = F₂ ((inj₂ M₂) , (inj₂ M₂'))

    F→F₁ : SubsetOf (TyCons × TyCons) 
         → SubsetOf ((IdTyCons ⊎ TyCons₁) × (IdTyCons ⊎ TyCons₁))
    F→F₁ F (M , M') = F (TC₁→TC M , TC₁→TC M')
    
    F→F₂ : SubsetOf (TyCons × TyCons) 
         → SubsetOf ((IdTyCons ⊎ TyCons₂) × (IdTyCons ⊎ TyCons₂))
    F→F₂ F (M , M') = F (TC₂→TC M , TC₂→TC M')
         
    
    mkFunctor : (M : TyCons₁ ⊎ TyCons₂) → B[ inj₂ M , idTC ] pm ▷ inj₂ M
    mkFunctor M = pmLawFunctor1 pm (inj₂ M)
    
    mkBindId : B[ idTC , idTC ] pm ▷ idTC
    mkBindId = pmLawFunctor1 pm idTC
    
    mkReturn : {N : TyCons₁ ⊎ TyCons₂}
             → (F : SubsetOf (TyCons × TyCons))
             → (idTC , idTC) ∈ F
             → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] polymonadCompose cpm₁ cpm₂ ▷ inj₂ N) 
             → B[ idTC , idTC ] polymonadCompose cpm₁ cpm₂ ▷ inj₂ N
    mkReturn F IdId∈F morph = morph idTC idTC IdId∈F
    
    mkMorph : {P : TyCons₁ ⊎ TyCons₂}
            → (N : TyCons₁ ⊎ TyCons₂)
            → (F : SubsetOf (TyCons × TyCons))
            → (inj₂ N , idTC) ∈ F
            → ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] polymonadCompose cpm₁ cpm₂ ▷ (inj₂ P)) 
            → B[ (inj₂ N) , idTC ] polymonadCompose cpm₁ cpm₂ ▷ (inj₂ P)
    mkMorph N F NId∈F morph = morph (inj₂ N) idTC NId∈F
    
    morph→morph₁ : {M̂ : IdTyCons ⊎ TyCons₁}
                 → (F : SubsetOf (TyCons × TyCons)) 
                 → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ TC₁→TC M̂)
                 → (∀ (M M' : IdTyCons ⊎ TyCons₁) → (M , M') ∈ F→F₁ F → B[ M , M' ] pm₁ ▷ M̂) 
    morph→morph₁ {M̂} F morph M M' MM'∈F₁ = subst (λ X → X) (sym (eqBindT₁ M M' M̂)) (morph (TC₁→TC M) (TC₁→TC M') MM'∈F₁)
    
    morph→morph₂ : {M̂ : IdTyCons ⊎ TyCons₂}
                 → (F : SubsetOf (TyCons × TyCons)) 
                 → (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ TC₂→TC M̂)
                 → (∀ (M M' : IdTyCons ⊎ TyCons₂) → (M , M') ∈ F→F₂ F → B[ M , M' ] pm₂ ▷ M̂) 
    morph→morph₂ {M̂} F morph M M' MM'∈F₂ = subst (λ X → X) (sym (eqBindT₂ M M' M̂)) (morph (TC₂→TC M) (TC₂→TC M') MM'∈F₂)
    
    -- B[M₁N₂]▷P≡⊥ : (M : TyCons₁) → (N : TyCons₂) → (P : TyCons) → B[ TC₁→TC (inj₂ M) , TC₂→TC (inj₂ N) ] pm ▷ P ≡ ⊥

    princRes₁→princRes : (F : SubsetOf (TyCons × TyCons))
                       → (M₁ M₂ : IdTyCons ⊎ TyCons₁)
                       → ( ∃ λ(M̂ : IdTyCons ⊎ TyCons₁) 
                         → B[ M̂ , idTC ] pm₁ ▷ M₁ 
                         × B[ M̂ , idTC ] pm₁ ▷ M₂ 
                         × (∀ (M M' : IdTyCons ⊎ TyCons₁) → (M , M') ∈ F→F₁ F → B[ M , M' ] pm₁ ▷ M̂))
                       → ( ∃ λ(M̂ : TyCons) 
                         → B[ M̂ , idTC ] pm ▷ TC₁→TC M₁ 
                         × B[ M̂ , idTC ] pm ▷ TC₁→TC M₂ 
                         × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
    princRes₁→princRes F M₁ M₂ (M̂ , b₁ , b₂ , morph) = TC₁→TC M̂ 
                                                     , subst (λ X → X) (eqBindT₁ M̂ idTC M₁) b₁ 
                                                     , subst (λ X → X) (eqBindT₁ M̂ idTC M₂) b₂ 
                                                     , {!!}
    
    
    princRes₂→princRes : (F : SubsetOf (TyCons × TyCons))
                       → (M₁ M₂ : IdTyCons ⊎ TyCons₂)
                       → ( ∃ λ(M̂ : IdTyCons ⊎ TyCons₂) 
                         → B[ M̂ , idTC ] pm₂ ▷ M₁ 
                         × B[ M̂ , idTC ] pm₂ ▷ M₂ 
                         × (∀ (M M' : IdTyCons ⊎ TyCons₂) → (M , M') ∈ F→F₂ F → B[ M , M' ] pm₂ ▷ M̂))
                       → ( ∃ λ(M̂ : TyCons) 
                         → B[ M̂ , idTC ] pm ▷ TC₂→TC M₁ 
                         × B[ M̂ , idTC ] pm ▷ TC₂→TC M₂ 
                         × (∀ (M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ M̂))
    princRes₂→princRes F M₁ M₂ (M̂ , b₁ , b₂ , morph) = TC₂→TC M̂ 
                                                     , subst (λ X → X) (eqBindT₂ M̂ idTC M₁) b₁ 
                                                     , subst (λ X → X) (eqBindT₂ M̂ idTC M₂) b₂ 
                                                     , {!!}
    -- eqBindT₁ : (M N P : IdTyCons ⊎ TyCons₁) → B[ M , N ] pm₁ ▷ P ≡ B[ TC₁→TC M , TC₁→TC N ] pm ▷ TC₁→TC P
    {-
    princ₁ : (F : SubsetOf ((IdTyCons ⊎ TyCons₁) × (IdTyCons ⊎ TyCons₁)))
           → (M₁ M₂ : IdTyCons ⊎ TyCons₁)
           → (∀ (M M' : IdTyCons ⊎ TyCons₁) → (M , M') ∈ F → B[ M , M' ] pm₁ ▷ M₁)
           → (∀ (M M' : IdTyCons ⊎ TyCons₁) → (M , M') ∈ F → B[ M , M' ] pm₁ ▷ M₂)
           → ∃ λ(M̂ : IdTyCons ⊎ TyCons₁) 
           → B[ M̂ , Id ] pm₁ ▷ M₁ 
           × B[ M̂ , Id ] pm₁ ▷ M₂ 
           × (∀ (M M' : IdTyCons ⊎ TyCons₁) → (M , M') ∈ F → B[ M , M' ] pm₁ ▷ M̂)
    -}

    morph₂¬∃ : (F : SubsetOf (TyCons × TyCons))
            → (M₁ : TyCons₁) → (N₂ : TyCons₂) → (N : TyCons)
            → ((inj₂ (inj₁ M₁) , N) ∈ F ⊎ (N , inj₂ (inj₁ M₁)) ∈ F) 
            → ¬ ((M M' : TyCons) → (M , M') ∈ F → B[ M , M' ] pm ▷ inj₂ (inj₂ N₂))
    morph₂¬∃ F M₁ N₂ (inj₁ IdentTC) (inj₁ MN∈F) morph = morph (inj₂ (inj₁ M₁)) idTC MN∈F
    morph₂¬∃ F M₁ N₂ (inj₁ IdentTC) (inj₂ NM∈F) morph = morph idTC (inj₂ (inj₁ M₁)) NM∈F
    morph₂¬∃ F M₁ N₂ (inj₂ (inj₁ N)) (inj₁ MN∈F) morph = morph (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N)) MN∈F
    morph₂¬∃ F M₁ N₂ (inj₂ (inj₁ N)) (inj₂ NM∈F) morph = morph (inj₂ (inj₁ N)) (inj₂ (inj₁ M₁)) NM∈F
    morph₂¬∃ F M₁ N₂ (inj₂ (inj₂ N)) (inj₁ MN∈F) morph = morph (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N)) MN∈F
    morph₂¬∃ F M₁ N₂ (inj₂ (inj₂ N)) (inj₂ NM∈F) morph = morph (inj₂ (inj₂ N)) (inj₂ (inj₁ M₁)) NM∈F

    princ : PrincipalPM (polymonadCompose cpm₁ cpm₂)
    princ F (inj₁ IdentTC  ) (inj₁ IdentTC  ) morph₁ morph₂ = inj₁ IdentTC , mkBindId , mkBindId , morph₂
    princ F (inj₁ IdentTC  ) (inj₂ (inj₁ N₁)) morph₁ morph₂ = princRes₁→princRes F (idTC   ) (inj₂ N₁) (princ₁ (F→F₁ F) (idTC   ) (inj₂ N₁) (morph→morph₁ F morph₁) (morph→morph₁ F morph₂))
    princ F (inj₁ IdentTC  ) (inj₂ (inj₂ N₂)) morph₁ morph₂ = princRes₂→princRes F (idTC   ) (inj₂ N₂) (princ₂ (F→F₂ F) (idTC   ) (inj₂ N₂) (morph→morph₂ F morph₁) (morph→morph₂ F morph₂))
    princ F (inj₂ (inj₁ M₁)) (inj₁ IdentTC  ) morph₁ morph₂ = princRes₁→princRes F (inj₂ M₁) (idTC   ) (princ₁ (F→F₁ F) (inj₂ M₁) (idTC   ) (morph→morph₁ F morph₁) (morph→morph₁ F morph₂))
    princ F (inj₂ (inj₁ M₁)) (inj₂ (inj₁ N₁)) morph₁ morph₂ = princRes₁→princRes F (inj₂ M₁) (inj₂ N₁) (princ₁ (F→F₁ F) (inj₂ M₁) (inj₂ N₁) (morph→morph₁ F morph₁) (morph→morph₁ F morph₂))
    princ F (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) morph₁ morph₂ with (inj₂ (inj₁ M₁) , inj₂ (inj₂ N₂)) ∈? F
    princ F (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) morph₁ morph₂ | yes MN∈F = ⊥-elim (morph₂¬∃ F M₁ N₂ (inj₂ (inj₂ N₂)) (inj₁ MN∈F) morph₂)
    princ F (inj₂ (inj₁ M₁)) (inj₂ (inj₂ N₂)) morph₁ morph₂ | no ¬MN∈F = {!!}
    -- inj₂ (inj₁ M₁) , mkFunctor (inj₁ M₁) , mkMorph (inj₁ M₁) F morph₂ , morph₁
    princ F (inj₂ (inj₂ M₂)) (inj₁ IdentTC  ) morph₁ morph₂ = princRes₂→princRes F (inj₂ M₂) (idTC   ) (princ₂ (F→F₂ F) (inj₂ M₂) (idTC   ) (morph→morph₂ F morph₁) (morph→morph₂ F morph₂))
    princ F (inj₂ (inj₂ M₂)) (inj₂ (inj₁ N₁)) morph₁ morph₂ = {!!}
    -- inj₂ (inj₂ M₂) , mkFunctor (inj₂ M₂) , mkMorph (inj₁ N₁) F morph₁ , morph₁
    princ F (inj₂ (inj₂ M₂)) (inj₂ (inj₂ N₂)) morph₁ morph₂ = princRes₂→princRes F (inj₂ M₂) (inj₂ N₂) (princ₂ (F→F₂ F) (inj₂ M₂) (inj₂ N₂) (morph→morph₂ F morph₁) (morph→morph₂ F morph₂))

    p : (M₁ : TyCons₁) → (M₂ : TyCons₂) 
      → (F : SubsetOf (TyCons × TyCons)) 
      → ¬ ((inj₂ (inj₁ M₁) , inj₂ (inj₂ M₂)) ∈ F)
      → ¬ ((inj₂ (inj₂ M₂) , inj₂ (inj₁ M₁)) ∈ F)
      → ¬ ((inj₂ (inj₁ M₁) , inj₁ IdentTC  ) ∈ F)
      → ¬ ((inj₁ IdentTC   , inj₂ (inj₁ M₁)) ∈ F)
      → ¬ ((inj₂ (inj₂ M₂) , inj₁ IdentTC  ) ∈ F)
      → ¬ ((inj₁ IdentTC   , inj₂ (inj₂ M₂)) ∈ F)
      → (∀ (M M' : TyCons) → F (M , M') ≡ false)
    p = {!!}

{-
¬principalPolymonadCompose : ∀ {TyCons₁ TyCons₂ : Set}
                           → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
                           → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
                           → (cpm₁ : ComposablePolymonad pm₁)
                           → (cpm₂ : ComposablePolymonad pm₂)
                           → PrincipalPM pm₁
                           → PrincipalPM pm₂
                           → ¬ (PrincipalPM (polymonadCompose cpm₁ cpm₂))
¬principalPolymonadCompose {TyCons₁} {TyCons₂} {pm₁} {pm₂} cpm₁ cpm₂ princ₁ princ₂ princ = empty
  where
    TyCons = IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)
    
    subsetAll : SubsetOf (TyCons × TyCons)
    subsetAll _ = true
    
    subsetId : SubsetOf (TyCons × TyCons)
    subsetId (inj₁ IdentTC , inj₁ IdentTC) = true
    subsetId (inj₁ IdentTC , inj₂ N) = false
    subsetId (inj₂ M , N) = false
    
    mkIdBind : B[ idTC , idTC ] polymonadCompose cpm₁ cpm₂ ▷ idTC
    mkIdBind = pmLawFunctor1 (polymonadCompose cpm₁ cpm₂) idTC
    
    morphId : (M M' : IdTyCons ⊎ TyCons₁ ⊎ TyCons₂) 
            → (M , M') ∈ subsetId 
            → B[ M , M' ] polymonadCompose cpm₁ cpm₂ ▷ idTC
    morphId (inj₁ IdentTC) (inj₁ IdentTC) refl = mkIdBind
    morphId (inj₁ IdentTC) (inj₂ M') ()
    morphId (inj₂ M) M' ()
    
    morphAll : (M M' : IdTyCons ⊎ TyCons₁ ⊎ TyCons₂) 
             → (M , M') ∈ subsetAll
             → B[ M , M' ] polymonadCompose cpm₁ cpm₂ ▷ idTC
    morphAll (inj₁ IdentTC  ) (inj₁ IdentTC   ) refl = mkIdBind
    morphAll (inj₁ IdentTC  ) (inj₂ (inj₁ M'₁)) refl = {!!}
    morphAll (inj₁ IdentTC  ) (inj₂ (inj₂ M'₂)) refl = {!!}
    morphAll (inj₂ (inj₁ M₁)) (inj₁ IdentTC   ) refl = {!!}
    morphAll (inj₂ (inj₁ M₁)) (inj₂ (inj₁ M'₁)) refl = {!!}
    morphAll (inj₂ (inj₁ M₁)) (inj₂ (inj₂ M'₂)) refl = {!!}
    morphAll (inj₂ (inj₂ M₂)) (inj₁ IdentTC   ) refl = {!!}
    morphAll (inj₂ (inj₂ M₂)) (inj₂ (inj₁ M'₁)) refl = {!!}
    morphAll (inj₂ (inj₂ M₂)) (inj₂ (inj₂ M'₂)) refl = {!!}
    
    empty : ⊥
    empty with princ subsetId idTC idTC morphId morphId
    empty | inj₁ IdentTC , b₁ , b₂ , morph' = {!!}
    empty | inj₂ (inj₁ M₁) , b₁ , b₂ , morph' = cpmIdMorph¬∃ cpm₁ (inj₁ (M₁ , refl)) b₁
    empty | inj₂ (inj₂ M₂) , b₁ , b₂ , morph' = cpmIdMorph¬∃ cpm₂ (inj₁ (M₂ , refl)) b₁

-}

