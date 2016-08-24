
module Theory.Examples.MonadToTwoFunctor where

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
                    → {C : Category {ℓC₀} {ℓC₁}} {M : Functor C C} 
                    →  Monad M → LaxTwoFunctor ⊤-TwoCat (functorTwoCategory {ℓC₀} {ℓC₁})
Monad→LaxTwoFunctor {ℓC₀} {ℓC₁} {C} {M} monad = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = ηP
  ; μ = μP
  ; laxFunId₁ = λ {x} {y} {f} → laxFunId₁ {x} {y} {f}
  ; laxFunId₂ = λ {x} {y} {f} → laxFunId₂ {x} {y} {f}
  ; laxFunAssoc = λ {x} {y} {z} {w} {f} {g} {h} → laxFunAssoc {x} {y} {z} {w} {f} {g} {h}
  } where
    open Category
    open NaturalTransformation
    FunTwoCat = functorTwoCategory {ℓC₀} {ℓC₁}
    
    _∘C_ = Category._∘_ C

    _∘V_ = _∘ᵥ_ FunTwoCat
    _∘H2_ = _∘ₕ₂_ FunTwoCat
    
    P₀ : Cell₀ ⊤-TwoCat → Cell₀ FunTwoCat
    P₀ tt = C
   
    ηF : (x : Obj C) → Hom C ([ M ]₀ x) ([ M ]₀ x)
    ηF x = Category.id C
        
    naturalF : {a b : Obj C} {f : Hom C a b} → [ M ]₁ f ∘C ηF a ≡ ηF b ∘C [ M ]₁ f
    naturalF {a} {b} {f} = trans (idL C) (sym (idR C))

    P₁ : {x y : Cell₀ ⊤-TwoCat} → Functor (HomCat ⊤-TwoCat x y) (HomCat FunTwoCat (P₀ x) (P₀ y))
    P₁ {tt} {tt} = record
      { F₀ = F₀
      ; F₁ = F₁
      ; id = refl
      ; dist = dist
      } where
        F₀ : ⊤ → Functor C C
        F₀ tt = M
        
        F₁ : {a b : Obj (HomCat ⊤-TwoCat tt tt)} 
           → Hom (HomCat ⊤-TwoCat tt tt) a b 
           → Hom (HomCat FunTwoCat (P₀ tt) (P₀ tt)) (F₀ a) (F₀ b)
        F₁ {tt} {tt} tt = naturalTransformation ηF naturalF
        
        dist : {a b c : Obj (HomCat ⊤-TwoCat tt tt)}
             → {f : Hom (HomCat ⊤-TwoCat tt tt) a b}
             → {g : Hom (HomCat ⊤-TwoCat tt tt) b c} 
             → F₁ ((HomCat ⊤-TwoCat tt tt ∘ g) f) 
             ≡ _∘_ (HomCat FunTwoCat C C) (F₁ g) (F₁ f)
        dist {tt} {tt} {tt} {tt} {tt} = 
          propEqNatTrans refl refl $ funExt $ λ (x : Obj C) → begin
            ηF x 
              ≡⟨ refl ⟩
            Category.id C
              ≡⟨ sym (idL C) ⟩
            Category.id C ∘C Category.id C
              ≡⟨ refl ⟩ 
            η ⟨ F₁ tt ⟩∘ᵥ⟨ F₁ tt ⟩ x ∎
    
    ηP : {x : Cell₀ ⊤-TwoCat} → Cell₂ FunTwoCat (id₁ FunTwoCat) ([ P₁ ]₀ (id₁ ⊤-TwoCat))
    ηP {tt} = Monad.η monad
    
    μP : {x y z : Cell₀ ⊤-TwoCat}
       → {f : Cell₁ ⊤-TwoCat x y} {g : Cell₁ ⊤-TwoCat y z}
       → Cell₂ FunTwoCat (_∘ₕ_ FunTwoCat ([ P₁ ]₀ g) ([ P₁ ]₀ f)) ([ P₁ ]₀ (_∘ₕ_ ⊤-TwoCat g f))
    μP {tt} {tt} {tt} {tt} {tt} = Monad.μ monad
        
    laxFunId₁ : {x y : Cell₀ ⊤-TwoCat} 
              → {f : Cell₁ ⊤-TwoCat x y}
              → [ P₁ ]₁ (λ' ⊤-TwoCat f) ∘V (μP ∘V ((id₂ FunTwoCat {f = M}) ∘H2 ηP)) 
              ≡ λ' FunTwoCat ([ P₁ ]₀ f)
    laxFunId₁ {tt} {tt} {tt} = propEqNatTrans refl refl $ funExt $ λ (x : Obj C) → begin
      η ([ P₁ ]₁ (λ' ⊤-TwoCat tt) ∘V (μP ∘V ((id₂ FunTwoCat {f = M}) ∘H2 ηP))) x
        ≡⟨ refl ⟩ 
      Category.id C ∘C (η μP x ∘C (Category.id C ∘C [ M ]₁ (η ηP x)))
        ≡⟨ cong (λ X → ηF x ∘C (η μP x ∘C X)) (idR C) ⟩ 
      Category.id C ∘C (η μP x ∘C [ M ]₁ (η ηP x))
        ≡⟨ idR C ⟩ 
      η (Monad.μ monad) x ∘C [ M ]₁ (η (Monad.η monad) x)
        ≡⟨ Monad.ηCoherL monad ⟩
      Category.id C
        ≡⟨ refl ⟩ 
      η (λ' FunTwoCat ([ P₁ ]₀ tt)) x ∎
    
    laxFunId₂ : {x y : Cell₀ ⊤-TwoCat} 
              → {f : Cell₁ ⊤-TwoCat x y}
              → [ P₁ ]₁ (ρ ⊤-TwoCat f) ∘V (μP ∘V (ηP ∘H2 (id₂ FunTwoCat {f = M}))) ≡ ρ FunTwoCat ([ P₁ ]₀ f)
    laxFunId₂ {tt} {tt} {tt} = propEqNatTrans refl refl $ funExt $ λ (x : Obj C) → begin
      η ([ P₁ ]₁ (ρ ⊤-TwoCat tt) ∘V (μP ∘V (ηP ∘H2 (id₂ FunTwoCat {f = M})))) x
        ≡⟨ refl ⟩
      Category.id C ∘C (η μP x ∘C (η ηP ([ M ]₀ x) ∘C Category.id C))
        ≡⟨ idR C ⟩
      η μP x ∘C (η ηP ([ M ]₀ x) ∘C Category.id C)
        ≡⟨ cong (λ X → η μP x ∘C X) (idL C) ⟩
      η μP x ∘C η ηP ([ M ]₀ x)
        ≡⟨ Monad.ηCoherR monad ⟩
      Category.id C -- η Id⟨ M ⟩ x
        ≡⟨ ≅-to-≡ $ subst₂-insert (sym (hIdR₁ FunTwoCat)) refl Id⟨ M ⟩ x ⟩
      η (subst₂ NaturalTransformation (sym (hIdR₁ FunTwoCat)) refl Id⟨ M ⟩) x
        ≡⟨ refl ⟩
      η (ρ FunTwoCat ([ P₁ ]₀ tt)) x ∎
    
    laxFunAssoc : {w x y z : Cell₀ ⊤-TwoCat}
                → {f : Cell₁ ⊤-TwoCat w x} {g : Cell₁ ⊤-TwoCat x y} {h : Cell₁ ⊤-TwoCat y z} 
                → [ P₁ ]₁ (α ⊤-TwoCat f g h) ∘V (μP ∘V (id₂ FunTwoCat {f = M} ∘H2 μP))
                ≡ μP ∘V ((μP ∘H2 (id₂ FunTwoCat {f = M})) ∘V α FunTwoCat ([ P₁ ]₀ f) ([ P₁ ]₀ g) ([ P₁ ]₀ h))
    laxFunAssoc {tt} {tt} {tt} {tt} {tt} {tt} {tt} = propEqNatTrans refl refl $ funExt $ λ (x : Obj C) → begin 
      η ([ P₁ ]₁ (α ⊤-TwoCat tt tt tt) ∘V (μP ∘V (id₂ FunTwoCat {f = M} ∘H2 μP))) x
        ≡⟨ refl ⟩
      Category.id C ∘C (η μP x ∘C (Category.id C ∘C [ M ]₁ (η μP x) ))
        ≡⟨ idR C ⟩
      η μP x ∘C (Category.id C ∘C [ M ]₁ (η μP x) )
        ≡⟨ cong (λ X → η μP x ∘C X) (idR C) ⟩
      η (Monad.μ monad) x ∘C [ M ]₁ (η (Monad.μ monad) x)
        ≡⟨ Monad.μCoher monad ⟩
      η (Monad.μ monad) x ∘C η (Monad.μ monad) ([ M ]₀ x)
        ≡⟨ cong (λ X → η μP x ∘C X) (sym (idL C)) ⟩
      η μP x ∘C ( η μP ([ M ]₀ x) ∘C Category.id C )
        ≡⟨ cong (λ X → η μP x ∘C ( η μP ([ M ]₀ x) ∘C X)) (sym (Functor.id M)) ⟩
      η μP x ∘C ( η μP ([ M ]₀ x) ∘C [ M ]₁ (Category.id C) )
        ≡⟨ cong (λ X → η μP x ∘C ( η μP ([ M ]₀ x) ∘C [ M ]₁ X )) (sym (Functor.id M)) ⟩
      η μP x ∘C ( η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) )
        ≡⟨ cong (λ X → η μP x ∘C X) (sym (idL C)) ⟩
      η μP x ∘C (( η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C Category.id C)
        ≡⟨ cong (λ X → η μP x ∘C (( η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C X)) (≅-to-≡ $ subst₂-insert refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩ x) ⟩
      η μP x ∘C (( η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∘C η (subst₂ NaturalTransformation refl (hAssoc₁ FunTwoCat {f = M} {M} {M}) Id⟨ [ M ]∘[ [ M ]∘[ M ] ] ⟩) x)
        ≡⟨ refl ⟩
      η (μP ∘V ((μP ∘H2 (id₂ FunTwoCat {f = M})) ∘V α FunTwoCat ([ P₁ ]₀ tt) ([ P₁ ]₀ tt) ([ P₁ ]₀ tt))) x ∎

