
module Theory.TwoFunctor.Properties.FromMonad where

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
  renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ; _≡⟨⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Haskell
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Definition hiding ( monad )
open import Theory.TwoCategory.Definition
open import Theory.TwoCategory.Examples.Functor
open import Theory.TwoCategory.Examples.Unit
open import Theory.TwoFunctor.Definition
open import Theory.TwoFunctor.ConstZeroCell

open StrictTwoCategory

Monad→ConstLaxTwoFunctor : ∀ {ℓC₀ ℓC₁} 
                         → {C : Category {ℓC₀} {ℓC₁}} {M : Functor C C} 
                         → Monad M → ConstLaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁}) C
Monad→ConstLaxTwoFunctor {ℓC₀} {ℓC₁} {C} {M} monad = record
  { P₁ = P₁
  ; η = ηP
  ; μ = μP
  ; laxFunId₁ = λ {x} {y} {f} → laxFunId₁ {x} {y} {f}
  ; laxFunId₂ = λ {x} {y} {f} → laxFunId₂ {x} {y} {f}
  ; laxFunAssoc = λ {x} {y} {z} {w} {f} {g} {h} → het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext hrefl $ laxFunAssoc {x} {y} {z} {w} {f} {g} {h}
  ; μ-natural₁ = λ _ → natural-transformation-eq $ fun-ext $ λ (c : Obj C) → trans (right-id C) (trans (sym (left-id C)) (cong (λ X → nat-η μP c ∘C X) (trans (sym (Functor.id M)) (sym (right-id C)))))
  ; μ-natural₂ = λ _ → natural-transformation-eq $ fun-ext $ λ (c : Obj C) → trans (right-id C) (trans (sym (left-id C)) (cong (λ X → nat-η μP c ∘C X) (trans (sym (Functor.id M)) (sym (right-id C)))))
  } where
    open Category
    open NaturalTransformation renaming ( η to nat-η )
    FunTwoCat = functorTwoCategory {ℓC₀} {ℓC₁}
    
    _∘C_ = Category._∘_ C
    
    P₀ : Cell₀ ⊤-TwoCat → Cell₀ FunTwoCat
    P₀ tt = C
   
    ηF : (x : Obj C) → Hom C ([ M ]₀ x) ([ M ]₀ x)
    ηF x = Category.id C
    
    abstract
      naturalF : {a b : Obj C} {f : Hom C a b} → [ M ]₁ f ∘C ηF a ≡ ηF b ∘C [ M ]₁ f
      naturalF {a} {b} {f} = trans (left-id C) (sym (right-id C))

    P₁ : {x y : Cell₀ ⊤-TwoCat} → Functor (HomCat ⊤-TwoCat x y) (HomCat FunTwoCat (P₀ x) (P₀ y))
    P₁ {tt} {tt} = record
      { F₀ = F₀
      ; F₁ = F₁
      ; id = refl
      ; compose = compose
      } where
        F₀ : ⊤ → Functor C C
        F₀ tt = M
        
        F₁ : {a b : Obj (HomCat ⊤-TwoCat tt tt)} 
           → Hom (HomCat ⊤-TwoCat tt tt) a b 
           → Hom (HomCat FunTwoCat (P₀ tt) (P₀ tt)) (F₀ a) (F₀ b)
        F₁ {tt} {tt} tt = Id⟨ F₀ tt ⟩
        
        abstract
          compose : {a b c : Obj (HomCat ⊤-TwoCat tt tt)}
                  → {f : Hom (HomCat ⊤-TwoCat tt tt) a b}
                  → {g : Hom (HomCat ⊤-TwoCat tt tt) b c} 
                  → F₁ (Category._∘_ (HomCat ⊤-TwoCat tt tt) g f) 
                  ≡ ⟨ F₁ g ⟩∘ᵥ⟨ F₁ f ⟩
          compose {tt} {tt} {tt} {tt} {tt} = 
            natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
              ηF x 
                ≡⟨ refl ⟩
              Category.id C
                ≡⟨ sym (left-id C) ⟩
              Category.id C ∘C Category.id C
                ≡⟨ refl ⟩ 
              nat-η ⟨ F₁ tt ⟩∘ᵥ⟨ F₁ tt ⟩ x ∎
    
    ηP : {x : Cell₀ ⊤-TwoCat} → Cell₂ FunTwoCat (id₁ FunTwoCat) ([ P₁ ]₀ (id₁ ⊤-TwoCat))
    ηP {tt} = Monad.η monad
    
    μP : {x y z : Cell₀ ⊤-TwoCat}
       → {f : Cell₁ ⊤-TwoCat x y} {g : Cell₁ ⊤-TwoCat y z}
       → Cell₂ FunTwoCat (StrictTwoCategory._∘_ FunTwoCat ([ P₁ ]₀ g) ([ P₁ ]₀ f)) ([ P₁ ]₀ (StrictTwoCategory._∘_ ⊤-TwoCat g f))
    μP {tt} {tt} {tt} {tt} {tt} = Monad.μ monad
        
    abstract
      laxFunId₁ : {x y : Cell₀ ⊤-TwoCat} 
                → {f : Cell₁ ⊤-TwoCat x y}
                → ⟨ μP ⟩∘ᵥ⟨ ⟨ id₂ FunTwoCat {f = M} ⟩∘ₕ⟨ ηP ⟩ ⟩
                ≅ id₂ FunTwoCat {C}
      laxFunId₁ {tt} {tt} {tt} = het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext hrefl $ λ (c : Obj C) → hbegin
        nat-η ⟨ μP ⟩∘ᵥ⟨ ⟨ id₂ FunTwoCat {f = M} ⟩∘ₕ⟨ ηP ⟩ ⟩ c
          ≅⟨ hrefl ⟩ 
        nat-η μP c ∘C (Category.id C ∘C [ M ]₁ (nat-η ηP c))
          ≅⟨ hcong (λ X → nat-η μP c ∘C X) (≡-to-≅ $ right-id C) ⟩ 
        nat-η μP c ∘C [ M ]₁ (nat-η ηP c)
          ≅⟨ ≡-to-≅ $ Monad.η-left-coher monad ⟩ 
        nat-η {F = M} (id₂ FunTwoCat {C}) c ∎h -- ≡-to-≅ $ Monad.η-left-coher monad
    
    abstract
      laxFunId₂ : {x y : Cell₀ ⊤-TwoCat} 
                → {f : Cell₁ ⊤-TwoCat x y}
                → ⟨ μP ⟩∘ᵥ⟨ ⟨ ηP ⟩∘ₕ⟨ id₂ FunTwoCat {f = M} ⟩ ⟩ ≅ id₂ FunTwoCat {C}
      laxFunId₂ {tt} {tt} {tt} = het-natural-transformation-eq (functor-eq refl hrefl) refl $ het-fun-ext hrefl $ λ (x : Obj C) → hbegin
        nat-η (⟨ μP ⟩∘ᵥ⟨ ⟨ ηP ⟩∘ₕ⟨ id₂ FunTwoCat {f = M} ⟩ ⟩) x
          ≅⟨ hrefl ⟩
        nat-η μP x ∘C (nat-η ηP ([ M ]₀ x) ∘C Category.id C)
          ≅⟨ hcong (λ X → nat-η μP x ∘C X) (≡-to-≅ (Category.left-id C)) ⟩
        nat-η μP x ∘C nat-η ηP ([ M ]₀ x)
          ≅⟨ ≡-to-≅ (Monad.η-right-coher monad) ⟩
        nat-η {F = M} (id₂ FunTwoCat {C}) x ∎h
    
    abstract
      laxFunAssoc : {w x y z : Cell₀ ⊤-TwoCat}
                  → {f : Cell₁ ⊤-TwoCat w x} {g : Cell₁ ⊤-TwoCat x y} {h : Cell₁ ⊤-TwoCat y z} 
                  → (x : Obj C)
                  → nat-η μP x ∘C (Category.id C ∘C [ M ]₁ (nat-η μP x) )
                  ≅ nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) )
      laxFunAssoc {tt} {tt} {tt} {tt} {tt} {tt} {tt} x = hbegin 
        nat-η μP x ∘C (Category.id C ∘C [ M ]₁ (nat-η μP x) )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μP x ∘C X) (right-id C) ⟩
        nat-η (Monad.μ monad) x ∘C [ M ]₁ (nat-η (Monad.μ monad) x)
          ≅⟨ ≡-to-≅ $ Monad.μ-coher monad ⟩
        nat-η (Monad.μ monad) x ∘C nat-η (Monad.μ monad) ([ M ]₀ x)
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μP x ∘C X) (sym (left-id C)) ⟩
        nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C Category.id C )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C X)) (sym (Functor.id M)) ⟩
        nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C [ M ]₁ (Category.id C) )
          ≅⟨ ≡-to-≅ $ cong (λ X → nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C [ M ]₁ X )) (sym (Functor.id M)) ⟩
        nat-η μP x ∘C ( nat-η μP ([ M ]₀ x) ∘C [ M ]₁ ([ M ]₁ (Category.id C)) ) ∎h


Monad→LaxTwoFunctor : ∀ {ℓC₀ ℓC₁} 
                    → {C : Category {ℓC₀} {ℓC₁}} {M : Functor C C} 
                    →  Monad M → LaxTwoFunctor ⊤-TwoCat (Cat {ℓC₀} {ℓC₁})
Monad→LaxTwoFunctor {ℓC₀} {ℓC₁} {C} {M} monad = ConstLaxTwoFunctor.laxTwoFunctor $ Monad→ConstLaxTwoFunctor monad
