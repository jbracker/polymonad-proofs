
module Theory.TwoCategory.Examples where

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
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad
open import Theory.TwoCategory
open import Theory.TwoFunctor

open import Theory.Category.Examples

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
  ; horizontalIdR₁ = λ {A} {B} {F} → horizontalIdR₁ {A = A} {B} {F}
  ; horizontalIdR₂ = λ {A} {B} {F} {G} {α} → horizontalIdR₂ {A = A} {B} {F} {G} {α}
  ; horizontalIdL₁ = refl
  ; horizontalIdL₂ = λ {A} {B} {F} {G} {α} → horizontalIdL₂ {A = A} {B} {F} {G} {α}
  ; horizontalAssoc₁ = λ {A} {B} {C} {D} {F} {G} {H} → horizontalAssoc₁ {ℓB₀ = ℓObj} {ℓHom} {ℓObj} {ℓHom} {A = A} {B} {C} {D} {F} {G} {H}
  ; horizontalAssoc₂ = λ {A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} → horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ}  
  ; whiskerCoher1' = λ {A} {B} {C} {D} {F} {G} {H} {I} {α} → whiskerCoher1 {A = A} {B} {C} {D} {F} {G} {H} {I} {α}
  ; whiskerCoher2' = λ {A} {B} {C} {D} {F} {G} {H} {I} {α} → whiskerCoher2 {A = A} {B} {C} {D} {F} {G} {H} {I} {α}
  ; whiskerCoher3' = λ {A} {B} {C} {D} {F} {G} {H} {I} {α} → whiskerCoher3 {A = A} {B} {C} {D} {F} {G} {H} {I} {α}
  ; whiskerCoher4' = λ {A} {B} {C} {F} {G} {H} {I} {α} {β} → whiskerCoher4 {A = A} {B} {C} {F} {G} {H} {I} {α} {β}
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
    
    open import Theory.Category.Examples renaming ( functorCategory to Fun )
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
    
    horizontalIdR₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F : Cell₁ A B}
                   → [ id₁ ]∘[ F ] ≡ F
    horizontalIdR₁ {A = A} {B} {F} = functor-eq refl refl
    
    horizontalAssoc₁ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                   → {F : Cell₁ A B} {G : Cell₁ B C} {H : Cell₁ C D} 
                   → [ H ]∘[ [ G ]∘[ F ] ] ≡ [ [ H ]∘[ G ] ]∘[ F ]
    horizontalAssoc₁ {A = A} {B} {C} {D} {F} {G} {H} = functor-eq refl refl
    
    horizontalIdL₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F G : Cell₁ A B} {α : Cell₂ F G} 
                   → ⟨_⟩∘ₕ⟨_⟩ {C = A} {A} {B} {F} {G} {Id[ A ]} {Id[ A ]} α (idC (HomCat A A)) ≡ α
    horizontalIdL₂ {A = A} {B} {F} {G} {α} = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (η (idC (HomCat A A) {a = Id[ A ]}) x)
          ≡⟨ refl ⟩
        η α ([ Id[ A ] ]₀ x) ∘B [ F ]₁ (idC A)
          ≡⟨ cong (λ X → η α ([ Id[ A ] ]₀ x) ∘B X) (Functor.id F) ⟩
        η α ([ Id[ A ] ]₀ x) ∘B idC B
          ≡⟨ Category.left-id B ⟩
        η α ([ Id[ A ] ]₀ x)
          ≡⟨ refl ⟩
        η α x ∎
      where _∘B_ = Category._∘_ B
    
    horizontalIdR₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁}
                   → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} 
                   → {F G : Cell₁ A B}
                   → {α : Cell₂ F G} 
                   → ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ ≡ subst₂ Cell₂ (sym horizontalIdR₁) (sym horizontalIdR₁) α
    horizontalIdR₂ {A = A} {B} {F} {G} {α} =
      natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
        η ⟨ idC (HomCat B B) {a = Id[ B ]} ⟩∘ₕ⟨ α ⟩ x 
          ≡⟨ refl ⟩
        Category.id B ∘B η α x
          ≡⟨ right-id B ⟩
        η α x
          ≡⟨ ≅-to-≡ (subst₂-insert (sym (horizontalIdR₁ {F = F})) (sym (horizontalIdR₁ {F = G})) α x) ⟩
        η (subst₂ Cell₂ (sym (horizontalIdR₁ {F = F})) (sym (horizontalIdR₁ {F = G})) α) x ∎
      where _∘B_ = _∘_ B
    
    horizontalAssoc₂ : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                     → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}}
                     → {F F' : Cell₁ A B} {G G' : Cell₁ B C} {H H' : Cell₁ C D}
                     → {α : Cell₂ H H'} {β : Cell₂ G G'} {γ : Cell₂ F F'}
                     → [ comp ]₁ (α , [ comp ]₁ (β , γ)) 
                     ≡ subst₂ (Hom (HomCat A D)) (sym $ horizontalAssoc₁ {F = F} {G} {H}) (sym $ horizontalAssoc₁ {F = F'} {G'} {H'}) ([ comp ]₁ ([ comp ]₁ (α , β) , γ))
    horizontalAssoc₂ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} {α} {β} {γ} = 
      natural-transformation-eq $ fun-ext $ λ x → ≅-to-≡ (htrans (lemma x) (subst₂-insert eqA eqB ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x))
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
                ≅⟨ hcong (λ X → η α ([ G' ]₀ ([ F' ]₀ x)) ∘D X) (≡-to-≅ $ Functor.compose H) ⟩
              η α ([ G' ]₀ ([ F' ]₀ x)) ∘D ( [ H ]₁ (η β ([ F' ]₀ x)) ∘D [ H ]₁ ([ G ]₁ (η γ x)) )
                ≅⟨ ≡-to-≅ $ assoc D ⟩
              ( η α ([ G' ]₀ ([ F' ]₀ x)) ∘D [ H ]₁ (η β ([ F' ]₀ x)) ) ∘D [ H ]₁ ([ G ]₁ (η γ x)) -- η ⟨ α ⟩∘ₕ⟨ β ⟩ ([ F' ]₀ x)
                ≅⟨ refl ⟩
              η ([ comp ]₁ ([ comp ]₁ (α , β) , γ)) x ∎h

    whiskerCoher1 : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                  → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}} 
                  → {F : Cell₁ A B} {G : Cell₁ B C} {H I : Cell₁ C D}
                  → {α : Cell₂ H I} 
                  → [ comp ]₁ (α , idC (HomCat A C) {a = [ G ]∘[ F ]}) 
                  ≡ subst₂ Cell₂ (sym $ horizontalAssoc₁ {F = F} {G} {H}) (sym $ horizontalAssoc₁ {F = F} {G} {I}) 
                           ([ comp ]₁ ([ comp ]₁ (α , idC (HomCat B C) {a = G}) , idC (HomCat A B) {a = F}))
    whiskerCoher1 {A = A} {B} {C} {D} {F} {G} {H} {I} {α} = natural-transformation-eq $ fun-ext $ (λ (x : Obj A) → 
      ≅-to-≡ $ htrans (lemma x) (subst₂-insert eqA eqB ([ comp ]₁ ([ comp ]₁ (α , idC (HomCat B C) {a = G}) , idC (HomCat A B) {a = F})) x))
      where
        _∘D_ = _∘_ D
        eqA = sym $ horizontalAssoc₁ {F = F} {G} {H}
        eqB = sym $ horizontalAssoc₁ {F = F} {G} {I}
        
        lemma : (x : Obj A) → η ([ comp ]₁ (α , idC (HomCat A C) {a = [ G ]∘[ F ]})) x ≅ η ([ comp ]₁ ([ comp ]₁ (α , idC (HomCat B C) {a = G}) , idC (HomCat A B) {a = F})) x
        lemma x = hbegin
          η ([ comp ]₁ (α , idC (HomCat A C) {a = [ G ]∘[ F ]})) x 
            ≅⟨ refl ⟩
          η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (Category.id C)
            ≅⟨ hcong (λ X → η α ([ G ]₀ ([ F ]₀ x)) ∘D X) (≡-to-≅ $ Functor.id H) ⟩
          η α ([ G ]₀ ([ F ]₀ x)) ∘D Category.id D
            ≅⟨ hcong (λ X → η α ([ G ]₀ ([ F ]₀ x)) ∘D X) (≡-to-≅ $ sym $ Functor.id H) ⟩
          η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C)
            ≅⟨ ≡-to-≅ $ sym $ left-id D ⟩
          ( η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C) ) ∘D idC D
            ≅⟨ hcong (λ X → ( η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C) ) ∘D X) (≡-to-≅ $ sym $ Functor.id H) ⟩
          ( η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C) ) ∘D [ H ]₁ (idC C)
            ≅⟨ hcong (λ X → ( η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C) ) ∘D ( [ H ]₁ X )) (≡-to-≅ $ sym $ Functor.id G) ⟩
          ( η α ([ G ]₀ ([ F ]₀ x)) ∘D [ H ]₁ (idC C) ) ∘D [ H ]₁ ([ G ]₁ (idC B))
            ≅⟨ refl ⟩
          η ([ comp ]₁ ([ comp ]₁ (α , idC (HomCat B C) {a = G}) , idC (HomCat A B) {a = F})) x ∎h

    whiskerCoher2 : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                  → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}} 
                  → {F : Cell₁ A B} {G H : Cell₁ B C} {I : Cell₁ C D}
                  → {α : Cell₂ G H} 
                  → [ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (α , idC (HomCat A B) {a = F}))
                  ≡ subst₂ (Hom (HomCat A D)) (sym $ horizontalAssoc₁ {F = F} {G} {I}) (sym $ horizontalAssoc₁ {F = F} {H} {I}) 
                           ([ comp ]₁ ([ comp ]₁ (idC (HomCat C D) {a = I} , α) , idC (HomCat A B) {a = F}))
    whiskerCoher2 {A = A} {B} {C} {D} {F} {G} {H} {I} {α} = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → 
      ≅-to-≡ $ htrans (lemma x) (subst₂-insert eqA eqB ([ comp ]₁ ([ comp ]₁ (idC (HomCat C D) {a = I} , α) , idC (HomCat A B) {a = F})) x)
      where
        eqA = sym $ horizontalAssoc₁ {F = F} {G} {I}
        eqB = sym $ horizontalAssoc₁ {F = F} {H} {I}
        
        _∘D_ = _∘_ D
        _∘C_ = _∘_ C
        
        lemma : (x : Obj A) 
              → η ([ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (α , idC (HomCat A B) {a = F}))) x
              ≅ η ([ comp ]₁ ([ comp ]₁ (idC (HomCat C D) {a = I} , α) , idC (HomCat A B) {a = F})) x
        lemma x = hbegin
          η ([ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (α , idC (HomCat A B) {a = F}))) x
            ≅⟨ refl ⟩
          idC D ∘D [ I ]₁ (η α ([ F ]₀ x) ∘C [ G ]₁ (idC B))
            ≅⟨ ≡-to-≅ $ right-id D ⟩
          [ I ]₁ (η α ([ F ]₀ x) ∘C [ G ]₁ (idC B))
            ≅⟨ ≡-to-≅ $ Functor.compose I ⟩
          [ I ]₁ (η α ([ F ]₀ x)) ∘D [ I ]₁ ([ G ]₁ (idC B))
            ≅⟨ hcong (λ X → X ∘D [ I ]₁ ([ G ]₁ (idC B))) (≡-to-≅ $ sym $ right-id D) ⟩
          ( idC D ∘D [ I ]₁ (η α ([ F ]₀ x)) ) ∘D [ I ]₁ ([ G ]₁ (idC B))
            ≅⟨ refl ⟩
          η ([ comp ]₁ ([ comp ]₁ (idC (HomCat C D) {a = I} , α) , idC (HomCat A B) {a = F})) x ∎h
 
    whiskerCoher3 : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁ ℓD₀ ℓD₁}
                  → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}} {D : Cell₀ {ℓD₀} {ℓD₁}} 
                  → {F G : Cell₁ A B} {H : Cell₁ B C} {I : Cell₁ C D}
                  → {α : Cell₂ F G} 
                  → [ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (idC (HomCat B C) {a = H} , α))
                  ≡ subst₂ (Hom (HomCat A D)) (sym $ horizontalAssoc₁ {F = F} {H} {I}) (sym $ horizontalAssoc₁ {F = G} {H} {I}) ([ comp ]₁ (idC (HomCat B D) {a = [ I ]∘[ H ]} , α))
    whiskerCoher3 {A = A} {B} {C} {D} {F} {G} {H} {I} {α} = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → 
      ≅-to-≡ $ htrans (lemma x) (subst₂-insert eqA eqB ([ comp ]₁ (idC (HomCat B D) {a = [ I ]∘[ H ]} , α)) x)
      where
        eqA = sym $ horizontalAssoc₁ {F = F} {H} {I}
        eqB = sym $ horizontalAssoc₁ {F = G} {H} {I}
        
        _∘D_ = _∘_ D
        _∘C_ = _∘_ C
        
        lemma : (x : Obj A) 
              → η ([ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (idC (HomCat B C) {a = H} , α))) x
              ≅ η ([ comp ]₁ (idC (HomCat B D) {a = [ I ]∘[ H ]} , α)) x
        lemma x = hbegin
          η ([ comp ]₁ (idC (HomCat C D) {a = I} , [ comp ]₁ (idC (HomCat B C) {a = H} , α))) x
            ≅⟨ refl ⟩ 
          idC D ∘D [ I ]₁ (idC C ∘C [ H ]₁ (η α x))
            ≅⟨ hcong (λ X → idC D ∘D [ I ]₁ X) (≡-to-≅ $ right-id C) ⟩ 
          idC D ∘D [ I ]₁ ([ H ]₁ (η α x))
            ≅⟨ refl ⟩ 
          η ([ comp ]₁ (idC (HomCat B D) {a = [ I ]∘[ H ]} , α)) x ∎h
    
    whiskerCoher4 : ∀ {ℓA₀ ℓA₁ ℓB₀ ℓB₁ ℓC₀ ℓC₁}
                  → {A : Cell₀ {ℓA₀} {ℓA₁}} {B : Cell₀ {ℓB₀} {ℓB₁}} {C : Cell₀ {ℓC₀} {ℓC₁}}
                  → {F G : Cell₁ A B} {H I : Cell₁ B C}
                  → {α : Cell₂ F G} {β : Cell₂ H I} 
                  → ⟨ [ comp ]₁ (idC (HomCat B C) {a = I} , α) ⟩∘ᵥ⟨ [ comp ]₁ (β , idC (HomCat A B) {a = F}) ⟩
                  ≡ ⟨ [ comp ]₁ (β , idC (HomCat A B) {a = G}) ⟩∘ᵥ⟨ [ comp ]₁ (idC (HomCat B C) {a = H} , α) ⟩
    whiskerCoher4 {A = A} {B} {C} {F} {G} {H} {I} {α} {β} = natural-transformation-eq $ fun-ext $ λ (x : Obj A) → begin
      η ⟨ [ comp ]₁ (idC (HomCat B C) {a = I} , α) ⟩∘ᵥ⟨ [ comp ]₁ (β , idC (HomCat A B) {a = F}) ⟩ x
        ≡⟨ refl ⟩
      ( idC C ∘C [ I ]₁ (η α x) ) ∘C ( η β ([ F ]₀ x) ∘C [ H ]₁ (idC B) )
        ≡⟨ cong (λ X → X ∘C ( η β ([ F ]₀ x) ∘C [ H ]₁ (idC B) )) (right-id C) ⟩ 
      [ I ]₁ (η α x) ∘C ( η β ([ F ]₀ x) ∘C [ H ]₁ (idC B) )
        ≡⟨ cong (λ X → [ I ]₁ (η α x) ∘C ( η β ([ F ]₀ x) ∘C X )) (Functor.id H) ⟩ 
      [ I ]₁ (η α x) ∘C ( η β ([ F ]₀ x) ∘C idC C )
        ≡⟨ cong (λ X → [ I ]₁ (η α x) ∘C X) (left-id C) ⟩ 
      [ I ]₁ (η α x) ∘C η β ([ F ]₀ x)
        ≡⟨ natural β ⟩ 
      η β ([ G ]₀ x) ∘C [ H ]₁ (η α x)
        ≡⟨ cong (λ X → η β ([ G ]₀ x) ∘C X) (sym (right-id C)) ⟩ 
      η β ([ G ]₀ x) ∘C ( idC C ∘C [ H ]₁ (η α x) )
        ≡⟨ cong (λ X → X ∘C ( idC C ∘C [ H ]₁ (η α x) )) (sym (left-id C)) ⟩ 
      ( η β ([ G ]₀ x) ∘C idC C ) ∘C ( idC C ∘C [ H ]₁ (η α x) )
        ≡⟨ cong (λ X → ( η β ([ G ]₀ x) ∘C X ) ∘C ( idC C ∘C [ H ]₁ (η α x) )) (sym (Functor.id H)) ⟩ 
      ( η β ([ G ]₀ x) ∘C [ H ]₁ (idC B) ) ∘C ( idC C ∘C [ H ]₁ (η α x) )
        ≡⟨ refl ⟩ 
      η ⟨ [ comp ]₁ (β , idC (HomCat A B) {a = G}) ⟩∘ᵥ⟨ [ comp ]₁ (idC (HomCat B C) {a = H} , α) ⟩ x ∎
      where _∘C_ = _∘_ C
