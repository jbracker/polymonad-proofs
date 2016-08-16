
module Theory.Examples.TwoCategory where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
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
open import Theory.TwoFunctor

open import Theory.Examples.Category

open NaturalTransformation

functorTwoCategory : ∀ {ℓObj ℓHom} → StrictTwoCategory
functorTwoCategory {ℓObj} {ℓHom} = record
  { Cell₀ = Cell₀ {ℓObj} {ℓHom}
  ; HomCat = HomCat
  ; comp = λ {A} {B} {C} → comp {A = A} {B} {C}
  ; id₁ = id₁
  ; horizontalIdR₁ = refl
  ; horizontalIdR₂ = {!!} -- λ {A} {B} {F} {G} {α} → horizontalIdR₂ {A = A} {B} {F} {G} {α}
  ; horizontalIdL₁ = {!!} -- λ {A} {B} {F} → horizontalIdL₁ {A = A} {B} {F}
  ; horizontalIdL₂ = {!!} -- λ {A} {B} {F} {G} {α} → horizontalIdL₂ {A = A} {B} {F} {G} {α}
  ; horizontalAssoc₁ = {!!} -- λ {A} {B} {C} {D} {F} {G} {H} → horizontalAssoc₁ {ℓB₀ = ℓObj} {ℓHom} {ℓObj} {ℓHom} {A = A} {B} {C} {D} {F} {G} {H}
  ; horizontalAssoc₂ = {!!} -- λ {A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} → horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ}  
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
    
    subst₂-insert : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                  → {A : Category {ℓA₀} {ℓA₁}} {B : Category {ℓB₀} {ℓB₁}} 
                  → {F F' G G' : Functor A B}
                  → (eqA : F ≡ F')
                  → (eqB : G ≡ G')
                  → (α : NaturalTransformation F G)
                  → (x : Obj A) 
                  → η α x ≅ η (subst₂ Cell₂ eqA eqB α) x
    subst₂-insert refl refl α x = refl

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
          ≡⟨ ≅-to-≡ (subst₂-insert (sym (horizontalIdL₁ {F = F})) (sym (horizontalIdL₁ {F = G})) α x) ⟩
        η (subst₂ Cell₂ (sym (horizontalIdL₁ {F = F})) (sym (horizontalIdL₁ {F = G})) α) x ∎
      where _∘B_ = _∘_ B

    horizontalAssoc₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                   → {F : Cell₁ A B} {G : Cell₁ B C} {H : Cell₁ C D} 
                   → [ H ]∘[ [ G ]∘[ F ] ] ≡ [ [ H ]∘[ G ] ]∘[ F ]
    horizontalAssoc₁ {A = A} {B} {C} {D} {F} {G} {H} = propEqFunctor refl refl
    
    horizontalAssoc₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                     → {F F' : Cell₁ A B} {G G' : Cell₁ B C} {H H' : Cell₁ C D}
                     → {α : Cell₂ H H'} {β : Cell₂ G G'} {γ : Cell₂ F F'}
                     → [ comp ]₁ (α , [ comp ]₁ (β , γ)) 
                     ≡ subst₂ (Hom (HomCat A D)) (sym $ horizontalAssoc₁ {F = F} {G} {H}) (sym $ horizontalAssoc₁ {F = F'} {G'} {H'}) ([ comp ]₁ ([ comp ]₁ (α , β) , γ))
    horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} = 
      propEqNatTrans refl refl $ funExt $ λ x → ≅-to-≡ (htrans (lemma x) (subst₂-insert eqA eqB ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x))
      where _∘D_ = _∘_ D
            _∘C_ = _∘_ C
            _∘B_ = _∘_ B
            
            eqA = sym $ horizontalAssoc₁ {F = F} {G} {H}
            eqB = sym $ horizontalAssoc₁ {F = F'} {G'} {H'}

            lemma : (x : Obj A) → η ([ comp ]₁ (α , [ comp ]₁ (β , γ))) x ≅ η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x
            lemma x = hbegin
              η ([ comp ]₁ (α , [ comp ]₁ (β , γ))) x 
                ≅⟨ refl ⟩
              η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ([ H ]₁ ((η β ([ F' ]₀ x)) ∘C [ G ]₁ (η γ x)))
                ≅⟨ hcong (λ X → η α ([ G' ]₀ ([ F' ]₀ x)) ∘D X) (≡-to-≅ $ Functor.dist H) ⟩
              η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ( [ H ]₁ (η β ([ F' ]₀ x)) ∘D [ H ]₁ ([ G ]₁ (η γ x)) )
                ≅⟨ ≡-to-≅ $ assoc D ⟩
              ( η α ([ G' ]₀ ([ F' ]₀ x)) ∘D [ H ]₁ (η β ([ F' ]₀ x)) ) ∘D [ H ]₁ ([ G ]₁ (η γ x)) -- η ⟨ α ⟩∘ₕ⟨ β ⟩ ([ F' ]₀ x)
                ≅⟨ refl ⟩
              η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x ∎h
