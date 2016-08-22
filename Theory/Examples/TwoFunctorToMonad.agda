
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
open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

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

Monad→LaxTwoFunctor : ∀ {ℓC₀ ℓC₁} 
                    → (F : LaxTwoFunctor ⊤-TwoCat (functorTwoCategory {ℓC₀} {ℓC₁})) → Monad ([ LaxTwoFunctor.P₁ F ]₀ tt)
Monad→LaxTwoFunctor {ℓC₀} {ℓC₁} F = record 
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

    η = NaturalTransformation.η ηNat
    μ = NaturalTransformation.η μNat
    
    _∘C_ = Category._∘_ C
    _∘V_ = StrictTwoCategory._∘ᵥ_ FunTwoCat
    _∘H2_ = StrictTwoCategory._∘ₕ₂_ FunTwoCat
    {-
    laxFunAssoc : [ LaxTwoFunctor.P₁ F ]₁ tt ∘V (μNat ∘V (id₂ FunTwoCat ∘H2 μNat))
                ≡ μNat ∘V ( (μNat ∘H2 id₂ FunTwoCat) ∘V (α FunTwoCat M M M) )
    laxFunAssoc = LaxTwoFunctor.laxFunAssoc F {tt} {tt} {tt} {tt} {tt} {tt} {tt}
    -}
    open Category
    
    μCoher : {x : Obj C} 
           → μ x ∘C [ M ]₁ (μ x) ≡ μ x ∘C μ ([ M ]₀ x)
    μCoher {x} = begin
      μ x ∘C [ M ]₁ (μ x) 
        ≡⟨ cong (λ X → μ x ∘C X) (sym $ idR C) ⟩
      μ x ∘C (Category.id C ∘C [ M ]₁ (μ x) )
        ≡⟨ sym $ idR C ⟩
      Category.id C ∘C (μ x ∘C (Category.id C ∘C [ M ]₁ (μ x) ))

        ≡⟨ {!LaxTwoFunctor.laxFunAssoc F!} ⟩
      μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C NaturalTransformation.η (subst₂ NaturalTransformation refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩) x)
        ≡⟨ cong (λ X → μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C X)) (sym $ ≅-to-≡ $ subst₂-insert refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩ x) ⟩
      μ x ∘C (( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C Category.id C)
        ≡⟨ cong (λ X → μ x ∘C X) (idL C) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) )
        ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ X )) (Functor.id M) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C [ M ]₁ (Category.id C) )
        ≡⟨ cong (λ X → μ x ∘C ( μ ([ M ]₀ x) ∘C X)) (Functor.id M) ⟩
      μ x ∘C ( μ ([ M ]₀ x) ∘C Category.id C )
        ≡⟨ cong (λ X → μ x ∘C X) (idL C) ⟩
      μ x ∘C μ ([ M ]₀ x) ∎
{-
        
      
-}




    ηCoherL : {x : Obj C} 
            → μ x ∘C [ M ]₁ (η x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
    ηCoherL {x} = {!!}

    ηCoherR : {x : Obj C} 
            → μ x ∘C η ([ M ]₀ x) ≡ η⟨ Id⟨ M ⟩ ⟩ x
    ηCoherR {x} = {!!}
    
{-



laxFunId₁ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (λ' C f)) 
            ∘Dᵥ ( (μ {x} {x} {y} {id₁ C {x}} {f}) 
            ∘Dᵥ   (id₂ D {f = [ P₁ {x} {y} ]₀ f} ∘Dₕ₂ η {x}) )
              ≡ λ' D ([ P₁ {x} {y} ]₀ f)
    
    laxFunId₂ : {x y : Cell₀ C} {f : Cell₁ C x y} 
              → ([ P₁ {x} {y} ]₁ (ρ C f)) 
            ∘Dᵥ ( (μ {x} {y} {y} {f} {id₁ C {y}}) 
            ∘Dᵥ   (η {y} ∘Dₕ₂ id₂ D {f = [ P₁ {x} {y} ]₀ f}) ) 
              ≡ ρ D ([ P₁ {x} {y} ]₀ f)

    laxFunAssoc : {w x y z : Cell₀ C} {f : Cell₁ C w x} {g : Cell₁ C x y} {h : Cell₁ C y z}
               → ([ P₁ {w} {z} ]₁ (α C f g h)) 
             ∘Dᵥ ( (μ {w} {y} {z} {g ∘Cₕ f} {h}) 
             ∘Dᵥ   (id₂ D {P₀ y} {P₀ z} {[ P₁ {y} {z} ]₀ h} ∘Dₕ₂ μ {w} {x} {y} {f} {g}) ) 
               ≡ μ {w} {x} {z} {f} {h ∘Cₕ g} 
             ∘Dᵥ ( (μ {x} {y} {z} {g} {h} ∘Dₕ₂ id₂ D {P₀ w} {P₀ x} {[ P₁ {w} {x} ]₀ f}) 
             ∘Dᵥ   (α D ([ P₁ {w} {x} ]₀ f) ([ P₁ {x} {y} ]₀ g) ([ P₁ {y} {z} ]₀ h)) )
-}
