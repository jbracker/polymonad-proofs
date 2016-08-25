
module Theory.Examples.TwoFunctorToMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
-- open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Utilities
open import Haskell
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Monad
open import Theory.TwoCategory
open import Theory.Examples.TwoCategory
open import Theory.TwoFunctor 

open StrictTwoCategory

LaxTwoFunctor→Monad : ∀ {ℓC₀ ℓC₁} 
                    → (F : LaxTwoFunctor ⊤-TwoCat (functorTwoCategory {ℓC₀} {ℓC₁})) → Monad ([ LaxTwoFunctor.P₁ F ]₀ tt)
LaxTwoFunctor→Monad {ℓC₀} {ℓC₁} F = record 
  { η = ηNat
  ; μ = μNat
  ; μCoher = μCoher
  ; ηCoherL = ηCoherL
  ; ηCoherR = ηCoherR
  } where
    FunTwoCat = functorTwoCategory {ℓC₀} {ℓC₁}
    
    C : Category {ℓC₀} {ℓC₁}
    C = LaxTwoFunctor.P₀ F tt
    
    M : Functor C C
    M = [ LaxTwoFunctor.P₁ F ]₀ tt
    
    ηNat : NaturalTransformation Id[ C ] M
    ηNat = LaxTwoFunctor.η F
    
    μNat : NaturalTransformation [ M ]∘[ M ] M
    μNat = LaxTwoFunctor.μ F

    natη = NaturalTransformation.η

    η = natη ηNat
    μ = natη μNat
    
    _∘C_ = Category._∘_ C
    _∘V_ = StrictTwoCategory._∘ᵥ_ FunTwoCat
    _∘H2_ = StrictTwoCategory._∘ₕ₂_ FunTwoCat
    
    open Category
    
    idLemma : [ LaxTwoFunctor.P₁ F ]₁ tt ≡ Id⟨ M ⟩
    idLemma = Functor.id (LaxTwoFunctor.P₁ F)
    
    laxFunAssoc : (x : Obj C)
                → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( Category.id C ∘C [ M ]₁ (μ x) ) )
                ≡ μ x ∘C ( ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C natη (α FunTwoCat M M M) x )
    laxFunAssoc x = cong (λ X → X x) $ extractPropEqNatTransEta (LaxTwoFunctor.laxFunAssoc F {tt} {tt} {tt} {tt} {tt} {tt} {tt})
    
    μCoher : {x : Obj C} 
           → μ x ∘C [ M ]₁ (μ x) ≡ μ x ∘C μ ([ M ]₀ x)
    μCoher {x} = begin
      μ x ∘C [ M ]₁ (μ x) 
        ≡⟨ cong (λ X → μ x ∘C X) (sym $ idR C) ⟩
      μ x ∘C (id C ∘C [ M ]₁ (μ x) )
        ≡⟨ sym $ idR C ⟩
      id C ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
        ≡⟨ refl ⟩
      natη Id⟨ M ⟩ x ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
        ≡⟨ cong (λ X → X ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
      natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
        ≡⟨ laxFunAssoc x ⟩
      μ x ∘C ( ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C natη (α FunTwoCat M M M) x )
        ≡⟨ refl ⟩
      μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C natη (subst₂ NaturalTransformation refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩) x)
        ≡⟨ cong (λ X → μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C X)) (sym $ ≅-to-≡ $ subst₂-insert refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩ x) ⟩
      μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C id C)
        ≡⟨ cong (λ X → μ x ∘C X) (idL C) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) )
        ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ X )) (Functor.id M) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ (id C) )
        ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C X)) (Functor.id M) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C id C )
        ≡⟨ cong (λ X → μ x ∘C X) (idL C) ⟩
      μ x ∘C μ ([ M ]₀ x) ∎

    laxFunId₁ : (x : Obj C)
              → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( id C ∘C [ M ]₁ (η x) ) )
              ≡ natη (λ' FunTwoCat M) x
    laxFunId₁ x = cong (λ X → X x) $ extractPropEqNatTransEta $ LaxTwoFunctor.laxFunId₁ F {tt} {tt} {tt}
    
    ηCoherL : {x : Obj C} 
            → μ x ∘C [ M ]₁ (η x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
    ηCoherL {x} = begin
      μ x ∘C [ M ]₁ (η x) 
        ≡⟨ sym $ idR C ⟩ 
      id C ∘C (μ x ∘C [ M ]₁ (η x))
        ≡⟨ cong (λ X → id C ∘C (μ x ∘C X)) (sym $ idR C) ⟩ 
      id C ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
        ≡⟨ refl ⟩
      natη Id⟨ M ⟩ x ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
        ≡⟨ cong (λ X → X ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
      natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
        ≡⟨ laxFunId₁ x ⟩
      natη (λ' FunTwoCat M) x
        ≡⟨ refl ⟩
      η⟨ Id⟨ M ⟩ ⟩ x ∎

    laxFunId₂ : (x : Obj C) 
              → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( η ([ M ]₀ x) ∘C id C ) )
              ≡ natη (ρ FunTwoCat M) x
    laxFunId₂ x = cong (λ X → X x) $ extractPropEqNatTransEta $ LaxTwoFunctor.laxFunId₂ F {tt} {tt} {tt}

    ηCoherR : {x : Obj C} 
            → μ x ∘C η ([ M ]₀ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
    ηCoherR {x} = begin
      μ x ∘C η ([ M ]₀ x) 
        ≡⟨ cong (λ X → μ x ∘C X) (sym $ idL C) ⟩
      μ x ∘C (η ([ M ]₀ x) ∘C id C)
        ≡⟨ sym $ idR C ⟩
      id C ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
        ≡⟨ refl ⟩
      natη Id⟨ M ⟩ x ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
        ≡⟨ cong (λ X → X ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
      natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
        ≡⟨ laxFunId₂ x ⟩
      natη (ρ FunTwoCat M) x
        ≡⟨ sym $ ≅-to-≡ $ subst₂-insert (sym (hIdR₁ FunTwoCat)) refl Id⟨ M ⟩ x ⟩
      η⟨ Id⟨ M ⟩ ⟩ x ∎
