
module Theory.Examples.Category where 

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( id to idF ; _∘_ to _∘F_ )
open import Data.Product
open import Relation.Binary using ( Preorder )
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong )
open import Relation.Binary.PropositionalEquality

--open import Utilities
open import Extensionality
open import ProofIrrelevance
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation

-- Category of sets and functions.
setCategory : {ℓ₀ : Level} → Category {ℓ₀ = lsuc ℓ₀}
setCategory {ℓ₀ = ℓ₀} = record
  { Obj = Set ℓ₀
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; left-id = refl
  ; right-id = refl
  }

-- Category that only contains the endomorphisms of the given category.
endomorphismCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀} {ℓ₁} → Category {ℓ₀} {ℓ₀ ⊔ ℓ₁}
endomorphismCategory {ℓ₀} {ℓ₁} C = record
  { Obj = Obj
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → _∘_ {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = assoc
  ; left-id = idL
  ; right-id = idR
  } where
    Obj : Set ℓ₀
    Obj = Category.Obj C
    
    Hom : Obj → Obj → Set (ℓ₀ ⊔ ℓ₁)
    Hom a b = Category.Hom C a b × a ≡ b
    
    _∘C_ = Category._∘_ C
    
    _∘_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    (f , refl) ∘ (g , refl) = f ∘C g , refl
    
    id : {a : Obj} → Hom a a
    id = Category.id C , refl

    assoc : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {h : Hom c d} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc {f = f , refl} {g , refl} {h , refl} = cong (λ X → X , refl) (Category.assoc C {f = f} {g} {h})
    
    idL : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f
    idL {f = f , refl} = cong (λ X → X , refl) (Category.left-id C {f = f})
    
    idR : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    idR {f = f , refl} = cong (λ X → X , refl) (Category.right-id C {f = f})

-- Category of categories and functors.
catCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = lsuc (ℓ₀ ⊔ ℓ₁)} {ℓ₁ = ℓ₀ ⊔ ℓ₁}
catCategory {ℓ₀} {ℓ₁} = record
  { Obj = Category {ℓ₀} {ℓ₁}
  ; Hom = λ C D → Functor C D
  ; _∘_ = [_]∘[_]
  ; id = λ {C} → Id[ C ]
  ; assoc = λ {a b c d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = idL
  ; right-id = idR
  } where
    assoc : {a b c d : Category} {f : Functor a b} {g : Functor b c} {h : Functor c d} 
          → [ h ]∘[ [ g ]∘[ f ] ] ≡ [ [ h ]∘[ g ] ]∘[ f ]
    assoc = functor-eq refl refl
    
    idR : {a b : Category} {f : Functor a b} → [ Id[ b ] ]∘[ f ] ≡ f
    idR = functor-eq refl refl

    idL : {a b : Category} {f : Functor a b} → [ f ]∘[ Id[ a ] ] ≡ f
    idL = refl

-- Category of functors and natural transformations
functorCategory : {Cℓ₀ Cℓ₁ Dℓ₀ Dℓ₁ : Level} → Category {Cℓ₀} {Cℓ₁} → Category {Dℓ₀} {Dℓ₁} → Category
functorCategory C D = record
  { Obj = Functor C D
  ; Hom = NaturalTransformation {C = C} {D}
  ; _∘_ = λ {F} {G} {H} → ⟨_⟩∘ᵥ⟨_⟩ {C = C} {D} {F} {G} {H}
  ; id = λ {F} → Id⟨ F ⟩
  ; assoc = natural-transformation-eq $ fun-ext $ λ _ → Category.assoc D
  ; left-id = natural-transformation-eq $ fun-ext $ λ _ → Category.left-id D
  ; right-id = natural-transformation-eq $ fun-ext $ λ _ → Category.right-id D
  }

-- Category formed by a preorder
preorderCategory : {ℓC ℓEq ℓOrd : Level} 
                 → (P : Preorder ℓC ℓEq ℓOrd) 
                 → ((a b : Preorder.Carrier P) → ProofIrrelevance (Preorder._∼_ P a b))
                 → Category
preorderCategory P proof-irr-≤ = record
  { Obj = Preorder.Carrier P
  ; Hom = _≤_
  ; _∘_ = _∘_
  ; id = id
  ; assoc = assoc
  ; left-id = idL
  ; right-id = idR
  } where
    _≤_ = Preorder._∼_ P
    
    id = Preorder.refl P
    
    ptrans = Preorder.trans P
    
    _∘_ : {a b c : Preorder.Carrier P} → b ≤ c → a ≤ b → a ≤ c
    _∘_ b≤c a≤b = Preorder.trans P a≤b b≤c
    
    assoc : {a b c d : Preorder.Carrier P} {f : a ≤ b} {g : b ≤ c} {h : c ≤ d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc {a} {b} {c} {d} {f} {g} {h} = proof-irr-≤ a d (ptrans (ptrans f g) h) (ptrans f (ptrans g h))
    
    idR : {a b : Preorder.Carrier P} {f : a ≤ b} → id ∘ f ≡ f
    idR {a} {b} {f} = proof-irr-≤ a b (ptrans f id) f

    idL : {a b : Preorder.Carrier P} {f : a ≤ b} → f ∘ id ≡ f
    idL {a} {b} {f} = proof-irr-≤ a b (ptrans id f) f
