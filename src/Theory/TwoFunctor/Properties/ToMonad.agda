
module Theory.TwoFunctor.Properties.ToMonad where

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
open import Extensionality
open import Haskell
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.Unit
open import Theory.TwoCategory.ExampleProperties
open import Theory.TwoFunctor.Definition

open StrictTwoCategory
open NaturalTransformation renaming ( η to nat-η ) 

LaxTwoFunctor→Monad : ∀ {ℓC₀ ℓC₁} 
                    → (F : LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁})) → Monad ([ LaxTwoFunctor.P₁ F ]₀ tt)
LaxTwoFunctor→Monad {ℓC₀} {ℓC₁} F = record 
  { η = ηNat
  ; μ = μNat
  ; μ-coher = μCoher
  ; η-left-coher = ηCoherL
  ; η-right-coher = ηCoherR
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
    _∘H2_ = StrictTwoCategory._∘ₕ_ FunTwoCat
    
    open Category
    
    abstract
      idLemma : [ LaxTwoFunctor.P₁ F ]₁ tt ≡ Id⟨ M ⟩
      idLemma = Functor.id (LaxTwoFunctor.P₁ F)
    
    abstract
      laxFunAssoc : (x : Obj C)
                  → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( Category.id C ∘C [ M ]₁ (μ x) ) )
                  ≡ μ x ∘C ( ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C natη (α FunTwoCat M M M) x )
      laxFunAssoc x = cong (λ X → X x) $ cong natη (LaxTwoFunctor.laxFunAssoc F {tt} {tt} {tt} {tt} {tt} {tt} {tt})
    
    abstract
      μCoher : {x : Obj C} 
             → μ x ∘C [ M ]₁ (μ x) ≡ μ x ∘C μ ([ M ]₀ x)
      μCoher {x} = begin
        μ x ∘C [ M ]₁ (μ x) 
          ≡⟨ cong (λ X → μ x ∘C X) (sym $ right-id C) ⟩
        μ x ∘C (id C ∘C [ M ]₁ (μ x) )
          ≡⟨ sym $ right-id C ⟩
        id C ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
          ≡⟨ refl ⟩
        natη Id⟨ M ⟩ x ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
          ≡⟨ cong (λ X → X ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
        natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (id C ∘C [ M ]₁ (μ x) ))
          ≡⟨ laxFunAssoc x ⟩
        μ x ∘C ( ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C natη (α FunTwoCat M M M) x )
          ≡⟨ refl ⟩
        μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C natη (subst₂ NaturalTransformation refl (StrictTwoCategory.assoc FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩) x)
          ≡⟨ cong (λ X → μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C X)) (sym $ ≅-to-≡ $ subst₂-insert refl (StrictTwoCategory.assoc FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩ x) ⟩
        μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) ) ∘C id C)
          ≡⟨ cong (λ X → μ x ∘C X) (left-id C) ⟩
        μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (id C)) )
          ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ X )) (Functor.id M) ⟩
        μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ (id C) )
          ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C X)) (Functor.id M) ⟩
        μ x ∘C ( μ ([ M ]₀ x) ∘C id C )
          ≡⟨ cong (λ X → μ x ∘C X) (left-id C) ⟩
        μ x ∘C μ ([ M ]₀ x) ∎

    abstract
      laxFunId₁ : (x : Obj C)
                → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( id C ∘C [ M ]₁ (η x) ) )
                ≡ natη (λ' FunTwoCat M) x
      laxFunId₁ x = cong (λ X → X x) $ cong natη $ LaxTwoFunctor.laxFunId₁ F {tt} {tt} {tt}
    
    abstract
      ηCoherL : {x : Obj C} 
              → μ x ∘C [ M ]₁ (η x) ≡ nat-η Id⟨ M ⟩ x
      ηCoherL {x} = begin
        μ x ∘C [ M ]₁ (η x) 
          ≡⟨ sym $ right-id C ⟩ 
        id C ∘C (μ x ∘C [ M ]₁ (η x))
          ≡⟨ cong (λ X → id C ∘C (μ x ∘C X)) (sym $ right-id C) ⟩ 
        id C ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
          ≡⟨ refl ⟩
        natη Id⟨ M ⟩ x ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
          ≡⟨ cong (λ X → X ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
        natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (id C ∘C [ M ]₁ (η x)))
          ≡⟨ laxFunId₁ x ⟩
        natη (λ' FunTwoCat M) x
          ≡⟨ sym $ ≅-to-≡ $ subst₂-insert (sym (StrictTwoCategory.left-id FunTwoCat)) refl Id⟨ M ⟩ x ⟩
        nat-η Id⟨ M ⟩ x ∎

    abstract
      laxFunId₂ : (x : Obj C) 
                → natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C ( μ x ∘C ( η ([ M ]₀ x) ∘C id C ) )
                ≡ natη (ρ FunTwoCat M) x
      laxFunId₂ x = cong (λ X → X x) $ cong natη $ LaxTwoFunctor.laxFunId₂ F {tt} {tt} {tt}
  
    abstract
      ηCoherR : {x : Obj C} 
              → μ x ∘C η ([ M ]₀ x) ≡ nat-η Id⟨ M ⟩ x
      ηCoherR {x} = begin
        μ x ∘C η ([ M ]₀ x) 
          ≡⟨ cong (λ X → μ x ∘C X) (sym $ left-id C) ⟩
        μ x ∘C (η ([ M ]₀ x) ∘C id C)
          ≡⟨ sym $ right-id C ⟩
        id C ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
          ≡⟨ refl ⟩
        natη Id⟨ M ⟩ x ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
          ≡⟨ cong (λ X → X ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))) (≅-to-≡ $ subst₂-replace Id⟨ M ⟩ ([ LaxTwoFunctor.P₁ F ]₁ tt) (≡-to-≅ $ sym $ idLemma) x) ⟩
        natη ([ LaxTwoFunctor.P₁ F ]₁ tt) x ∘C (μ x ∘C (η ([ M ]₀ x) ∘C id C))
          ≡⟨ laxFunId₂ x ⟩
        natη (ρ FunTwoCat M) x
          ≡⟨ sym $ ≅-to-≡ $ subst₂-insert (sym (StrictTwoCategory.right-id FunTwoCat)) refl Id⟨ M ⟩ x ⟩
        nat-η Id⟨ M ⟩ x ∎

