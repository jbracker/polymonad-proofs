
module Theory.Examples.TwoCategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 

-- Local
open import Utilities
open import Haskell
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation
open import Theory.Monad
open import Theory.TwoCategory
open import Theory.TwoFunctor

open NaturalTransformation

functorTwoCategory : ∀ {ℓObj ℓHom} → StrictTwoCategory
functorTwoCategory {ℓObj} {ℓHom} = record
  { Cell₀ = Cell₀ {ℓObj} {ℓHom}
  ; HomCat = HomCat
  ; comp = λ {A} {B} {C} → comp {A = A} {B} {C}
  ; id₁ = id₁
  ; horizontalIdR₁ = refl
  ; horizontalIdR₂ = horizontalIdR₂
  ; horizontalIdL₁ = horizontalIdL₁
  ; horizontalIdL₂ = {!!}
  ; horizontalAssoc₁ = λ {A} {B} {C} {D} {F} {G} {H} → horizontalAssoc₁ {ℓB₀ = ℓObj} {ℓHom} {ℓObj} {ℓHom} {A = A} {B} {C} {D} {F} {G} {H}
  ; horizontalAssoc₂ = {!!}
  ; whiskerCoher1' = {!!}
  ; whiskerCoher2' = {!!}
  ; whiskerCoher3' = {!!}
  ; whiskerCoher4' = {!refl!}
  } where
    open Category renaming ( id to idC )
    
    Cell₀ = Category
    
    Cell₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁} 
          → Cell₀ {ℓA₀} {ℓA₁} → Cell₀ {ℓB₀} {ℓB₁} → Set (ℓB₁ ⊔ ℓB₀ ⊔ ℓA₁ ⊔ ℓA₀)
    Cell₁ A B = Functor A B
    
    Cell₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
          → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
          → Cell₁ A B → Cell₁ A B → Set (ℓB₁ ⊔ ℓB₀ ⊔ ℓA₁ ⊔ ℓA₀)
    Cell₂ {A = A} {B} F G = NaturalTransformation F G
    
    open import Theory.Examples.Category renaming ( functorCategory to Fun )
    open import Theory.Examples.Functor renaming ( natTransCompositionHorzFunctor to CompFunc )
    
    HomCat : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁} 
           → Cell₀ {ℓA₀} {ℓA₁} → Cell₀ {ℓB₀} {ℓB₁} → Category
    HomCat = Fun
    
    comp : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁} 
         → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}}
         → Functor (HomCat B C ×C HomCat A B) (HomCat A C)
    comp = CompFunc
    
    id₁ : ∀ {ℓA₀ ℓA₁} → {A : Cell₀ {ℓA₀} {ℓA₁}} → Cell₁ A A
    id₁ {A = A} = Id[ A ]

    horizontalIdR₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F G : Cell₁ A B} {α : Cell₂ F G} 
                   → ⟨_⟩∘ₕ⟨_⟩ {C = A} {A} {B} {F} {G} {Id[ A ]} {Id[ A ]} α (idC (HomCat A A)) ≡ α
    horizontalIdR₂ {A = A} {B} {F} {G} {α} = propEqNatTrans refl refl $ funExt $ λ (x : Obj A) → begin
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (η (idC (HomCat A A) {a = Id[ A ]}) x)
          ≡⟨ refl ⟩
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (idC A)
          ≡⟨ cong (λ X → η α ([ Id[ A ] ]₀ x) ∘B X) (Functor.id F) ⟩
        η α ([ Id[ A ] ]₀ x) ∘B idC B
          ≡⟨  Category.idR B ⟩
        η α ([ Id[ A ] ]₀ x)
          ≡⟨ refl ⟩
        η α x ∎
      where _∘B_ = Category._∘_ B

    horizontalIdL₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F : Cell₁ A B}
                   → [ id₁ ]∘[ F ] ≡ F
    horizontalIdL₁ {A = A} {B} {F} = propEqFunctor refl refl
{-
    horizontalIdL₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F G : Cell₁ A B}
                   → {α : Cell₂ F G} 
                   → ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ ≡ subst₂ Cell₂ (sym horizontalIdL₁) (sym horizontalIdL₁) α
    horizontalIdL₂ {A = A} {B} {F} {G} {α} =
      propEqNatTrans refl refl $ funExt $ λ (x : Obj A) → begin
        η ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ x 
          ≡⟨ refl ⟩
        Category.id B ∘B η α x
          ≡⟨ idL B ⟩
        η α x
          ≡⟨ lemma x ⟩
        η (subst₂ Cell₂ (sym (horizontalIdL₁ {F = F})) (sym (horizontalIdL₁ {F = G})) α) x ∎
      where 
        _∘B_ = _∘_ B
        
        lemma : (x : Obj A) 
              → η α x ≡ η (subst₂ Cell₂ (sym (horizontalIdL₁ {F = F})) (sym (horizontalIdL₁ {F = G})) α) x
        lemma x = begin
          η α x 
            ≡⟨ {!!} ⟩
          η (subst₂ Cell₂ (sym (horizontalIdL₁ {F = F})) (sym (horizontalIdL₁ {F = G})) α) x ∎
-}
    horizontalAssoc₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                   → {F : Cell₁ A B} {G : Cell₁ B C} {H : Cell₁ C D} 
                   → [ H ]∘[ [ G ]∘[ F ] ] ≡ [ [ H ]∘[ G ] ]∘[ F ]
    horizontalAssoc₁ {A = A} {B} {C} {D} {F} {G} {H} = propEqFunctor refl refl
    
