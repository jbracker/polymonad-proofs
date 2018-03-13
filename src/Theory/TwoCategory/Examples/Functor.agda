
module Theory.TwoCategory.Examples.Functor where

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
open import Extensionality
open import Haskell
open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Definition
open import Theory.TwoCategory.Definition
open import Theory.TwoFunctor.Definition

open NaturalTransformation

-------------------------------------------------------------------------------
-- Strict 2-Category of categories, functors and natural transformations
-------------------------------------------------------------------------------

functorTwoCategory : ∀ {ℓObj ℓHom} → StrictTwoCategory
functorTwoCategory {ℓObj} {ℓHom} = record
  { Cell₀ = Cell₀ {ℓObj} {ℓHom}
  ; HomCat = HomCat
  ; comp = λ {A} {B} {C} → comp {A = A} {B} {C}
  ; id₁ = id₁
  ; right-id = λ {A} {B} {F} → horizontalIdR₁ {A = A} {B} {F}
  ; horizontal-right-id = λ {A} {B} {F} {G} {α} → horizontalIdR₂ {A = A} {B} {F} {G} {α}
  ; left-id = λ {A} {B} {F} → horizontalIdL₁ {A = A} {B} {F}
  ; horizontal-left-id = λ {A} {B} {F} {G} {α} → horizontalIdL₂ {A = A} {B} {F} {G} {α}
  ; assoc = λ {A} {B} {C} {D} {F} {G} {H} → horizontalAssoc₁ {ℓB₀ = ℓObj} {ℓHom} {ℓObj} {ℓHom} {A = A} {B} {C} {D} {F} {G} {H}
  ; horizontal-assoc = λ {A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} → horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ}
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
    
    open import Theory.Category.Examples.Functor renaming ( functorCategory to Fun )
    open import Theory.Functor.Examples renaming ( natTransCompositionHorzFunctor to CompFunc )
    
    HomCat : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁} 
           → Cell₀ {ℓA₀} {ℓA₁} → Cell₀ {ℓB₀} {ℓB₁} → Category
    HomCat = Fun
    
    comp : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁} 
         → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}}
         → Functor (HomCat B C ×C HomCat A B) (HomCat A C)
    comp = CompFunc
    
    id₁ : ∀ {ℓA₀ ℓA₁} → {A : Cell₀ {ℓA₀} {ℓA₁}} → Cell₁ A A
    id₁ {A = A} = Id[ A ]
    
    abstract
      horizontalIdR₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                     → {F : Cell₁ A B}
                     → [ id₁ ]∘[ F ] ≡ F
      horizontalIdR₁ {A = A} {B} {F} = functor-eq refl refl
    
    abstract
      horizontalIdL₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                     → {F : Cell₁ A B}
                     → [ F ]∘[ id₁ ] ≡ F
      horizontalIdL₁ {A = A} {B} {F} = functor-eq refl refl
    
    abstract
      horizontalAssoc₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                       → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                       → {F : Cell₁ A B} {G : Cell₁ B C} {H : Cell₁ C D} 
                       → [ H ]∘[ [ G ]∘[ F ] ] ≡ [ [ H ]∘[ G ] ]∘[ F ]
      horizontalAssoc₁ {A = A} {B} {C} {D} {F} {G} {H} = functor-eq refl refl

    abstract
      subst-eq : {ℓA₀ ℓA₁ ℓB₀ ℓB₁ : Level} {a : Cell₀ {ℓA₀} {ℓA₁}} {b : Cell₀ {ℓB₀} {ℓB₁}} {f g f' g' : Obj (HomCat a b)} {α : Hom (HomCat a b) f' g'} {β : Hom (HomCat a b) f g} 
               → (p : f ≡ f') → (q : g ≡ g') 
               →  α ≅ β 
               → α ≡ subst₂ (Hom (HomCat a b)) p q β
      subst-eq refl refl refl = refl
    
    abstract
      horizontalIdL₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                     → {F G : Cell₁ A B} {α : Cell₂ F G} 
                     → ⟨_⟩∘ₕ⟨_⟩ {C = A} {A} {B} {F} {G} {Id[ A ]} {Id[ A ]} α (idC (HomCat A A)) ≅ α
      horizontalIdL₂ {A = A} {B} {F} {G} {α} = het-natural-transformation-eq (horizontalIdL₁ {A = A} {B} {F}) (horizontalIdL₁ {A = A} {B} {G}) $ het-fun-ext refl $ λ (x : Obj A) → hbegin
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (η (idC (HomCat A A) {a = Id[ A ]}) x)
          ≅⟨ refl ⟩
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (idC A)
          ≅⟨ ≡-to-≅ (cong (λ X → η α ([ Id[ A ] ]₀ x) ∘B X) (Functor.id F)) ⟩
        η α ([ Id[ A ] ]₀ x) ∘B idC B
          ≅⟨ ≡-to-≅ (Category.left-id B) ⟩
        η α ([ Id[ A ] ]₀ x)
          ≅⟨ refl ⟩
        η α x ∎h
        where _∘B_ = Category._∘_ B
    
    abstract
      horizontalIdR₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                     → {F G : Cell₁ A B}
                     → {α : Cell₂ F G} 
                     → ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ ≅ α
      horizontalIdR₂ {A = A} {B} {F} {G} {α} = het-natural-transformation-eq horizontalIdR₁ horizontalIdR₁ $ het-fun-ext refl $ λ (x : Obj A) → hbegin
          η ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ x 
            ≅⟨ refl ⟩
          Category.id B ∘B η α x
            ≅⟨ ≡-to-≅ (right-id B) ⟩
          η α x ∎h
        where _∘B_ = _∘_ B
    
    abstract
      horizontalAssoc₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                       → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                       → {F F' : Cell₁ A B} {G G' : Cell₁ B C} {H H' : Cell₁ C D}
                       → {α : Cell₂ H H'} {β : Cell₂ G G'} {γ : Cell₂ F F'}
                       → [ comp ]₁ (α , [ comp ]₁ (β , γ)) ≅ ([ comp ]₁ ([ comp ]₁ (α , β) , γ))
      horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} = 
        het-natural-transformation-eq horizontalAssoc₁ horizontalAssoc₁ $ het-fun-ext refl $ λ (x : Obj A) → hbegin
          η ([ comp ]₁ (α , [ comp ]₁ (β , γ))) x 
            ≅⟨ refl ⟩
          η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ([ H ]₁ ((η β ([ F' ]₀ x)) ∘C [ G ]₁ (η γ x)))
            ≅⟨ hcong (λ X → η α ([ G' ]₀ ([ F' ]₀ x)) ∘D X) (≡-to-≅ $ Functor.compose H) ⟩
          η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ( [ H ]₁ (η β ([ F' ]₀ x)) ∘D [ H ]₁ ([ G ]₁ (η γ x)) )
            ≅⟨ ≡-to-≅ $ assoc D ⟩
          ( η α ([ G' ]₀ ([ F' ]₀ x)) ∘D [ H ]₁ (η β ([ F' ]₀ x)) ) ∘D [ H ]₁ ([ G ]₁ (η γ x)) -- η ⟨ α ⟩∘ₕ⟨ β ⟩ ([ F' ]₀ x)
            ≅⟨ refl ⟩
          η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x ∎h
        where _∘D_ = _∘_ D
              _∘C_ = _∘_ C
              _∘B_ = _∘_ B
              
              eqA = sym $ horizontalAssoc₁ {F = F} {G} {H}
              eqB = sym $ horizontalAssoc₁ {F = F'} {G'} {H'}
              
              abstract
                lemma : (x : Obj A) → η ([ comp ]₁ (α , [ comp ]₁ (β , γ))) x ≅ η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x
                lemma x = hbegin
                  η ([ comp ]₁ (α , [ comp ]₁ (β , γ))) x 
                    ≅⟨ refl ⟩
                  η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ([ H ]₁ ((η β ([ F' ]₀ x)) ∘C [ G ]₁ (η γ x)))
                    ≅⟨ hcong (λ X → η α ([ G' ]₀ ([ F' ]₀ x)) ∘D X) (≡-to-≅ $ Functor.compose H) ⟩
                  η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ( [ H ]₁ (η β ([ F' ]₀ x)) ∘D [ H ]₁ ([ G ]₁ (η γ x)) )
                    ≅⟨ ≡-to-≅ $ assoc D ⟩
                  ( η α ([ G' ]₀ ([ F' ]₀ x)) ∘D [ H ]₁ (η β ([ F' ]₀ x)) ) ∘D [ H ]₁ ([ G ]₁ (η γ x)) -- η ⟨ α ⟩∘ₕ⟨ β ⟩ ([ F' ]₀ x)
                    ≅⟨ refl ⟩
                  η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x ∎h
                
    

Cat = functorTwoCategory
