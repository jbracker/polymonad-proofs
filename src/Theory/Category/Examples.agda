
module Theory.Category.Examples where 

-- Stdlib
open import Level
open import Function renaming ( id to idF ; _∘_ to _∘F_ )

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit hiding ( _≤_ )
open import Data.Bool

open import Relation.Binary using ( Preorder )
open import Relation.Binary.HeterogeneousEquality renaming ( cong to hcong ; proof-irrelevance to het-proof-irrelevance )
open import Relation.Binary.PropositionalEquality

--open import Utilities
open import Extensionality
open import Equality
open import ProofIrrelevance
open import Bijection renaming ( refl to brefl )
open import Theory.Category
open import Theory.Category.Isomorphism
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

-- Category of sets and functions.
setCategory : {ℓ : Level} → Category {ℓ₀ = suc ℓ} {ℓ}
setCategory {ℓ} = record
  { Obj = Set ℓ
  ; Hom = λ a b → (a → b)
  ; _∘_ = λ f g → f ∘F g
  ; id = idF
  ; assoc = refl
  ; left-id = refl
  ; right-id = refl
  }

-- Category that only has identity morphisms.
discreteCategory : {ℓ₀ : Level} → (A : Set ℓ₀) → Category {ℓ₀} {ℓ₀}
discreteCategory {ℓ₀} A = category A (λ a b → a ≡ b) comp (λ {a} → refl) assoc left-id right-id
  where
    comp : {a b c : A} → b ≡ c → a ≡ b → a ≡ c
    comp refl refl = refl
    
    assoc : {a b c d : A} {f : a ≡ b} {g : b ≡ c} {h : c ≡ d}
          → comp h (comp g f) ≡ comp (comp h g) f
    assoc {f = refl} {refl} {refl} = refl
    
    left-id : {a b : A} {f : a ≡ b} → comp refl f ≡ f
    left-id {f = refl} = refl
    
    right-id : {a b : A} {f : a ≡ b} → comp f refl ≡ f
    right-id {f = refl} = refl

SetIsomorphism↔Bijection : {ℓ : Level} {A B : Set ℓ} → (Σ (A → B) (Isomorphism (setCategory {ℓ}))) ↔ (Bijection A B)
SetIsomorphism↔Bijection {ℓ} {A} {B} = bijection Iso→Bij Bij→Iso right-id left-id
  where
    Iso→Bij : Σ (A → B) (Isomorphism setCategory) → Bijection A B
    Iso→Bij (f , iso) = bijection f (Isomorphism.inv iso) (λ x → cong (λ g → g x) (Isomorphism.left-id iso)) (λ x → cong (λ g → g x) (Isomorphism.right-id iso))
    
    Bij→Iso : (bij : Bijection A B) → Σ (A → B) (Isomorphism setCategory)
    Bij→Iso bij = Bijection.f bij ,  isomorphism (Bijection.inv bij) (fun-ext (Bijection.right-id bij)) (fun-ext (Bijection.left-id bij))

    right-id : (b : Bijection A B) → Iso→Bij (Bij→Iso b) ≡ b
    right-id bij = bijection-eq (inj₁ refl)
    
    left-id : (a : Σ (A → B) (Isomorphism setCategory)) → Bij→Iso (Iso→Bij a) ≡ a
    left-id (f , iso) = Σ-eq refl (≡-to-≅ (isomorphism-eq refl))

-- Category that only contains the endomorphisms of the given category.
endomorphismCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀} {ℓ₁} → Category {ℓ₀} {ℓ₀ ⊔ ℓ₁}
endomorphismCategory {ℓ₀} {ℓ₁} C = record
  { Obj = Obj
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → _∘_ {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = assoc
  ; left-id = left-id
  ; right-id = right-id
  } where
    open import Data.Product
    
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
    
    left-id : {a b : Obj} {f : Hom a b} → f ∘ id ≡ f
    left-id {f = f , refl} = cong (λ X → X , refl) (Category.left-id C {f = f})
    
    right-id : {a b : Obj} {f : Hom a b} → id ∘ f ≡ f
    right-id {f = f , refl} = cong (λ X → X , refl) (Category.right-id C {f = f})

-- Category of categories and functors.
catCategory : {ℓ₀ ℓ₁ : Level} → Category {ℓ₀ = suc (ℓ₀ ⊔ ℓ₁)} {ℓ₁ = ℓ₀ ⊔ ℓ₁}
catCategory {ℓ₀} {ℓ₁} = record
  { Obj = Category {ℓ₀} {ℓ₁}
  ; Hom = λ C D → Functor C D
  ; _∘_ = [_]∘[_]
  ; id = λ {C} → Id[ C ]
  ; assoc = λ {a b c d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = left-id
  ; right-id = right-id
  } where
    assoc : {a b c d : Category} {f : Functor a b} {g : Functor b c} {h : Functor c d} 
          → [ h ]∘[ [ g ]∘[ f ] ] ≡ [ [ h ]∘[ g ] ]∘[ f ]
    assoc = functor-eq refl refl
    
    right-id : {a b : Category} {f : Functor a b} → [ Id[ b ] ]∘[ f ] ≡ f
    right-id = functor-eq refl refl

    left-id : {a b : Category} {f : Functor a b} → [ f ]∘[ Id[ a ] ] ≡ f
    left-id = refl

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
  ; left-id = left-id
  ; right-id = right-id
  } where
    _≤_ = Preorder._∼_ P
    id = Preorder.refl P
    ptrans = Preorder.trans P
    
    _∘_ : {a b c : Preorder.Carrier P} → b ≤ c → a ≤ b → a ≤ c
    _∘_ b≤c a≤b = Preorder.trans P a≤b b≤c
    
    assoc : {a b c d : Preorder.Carrier P} {f : a ≤ b} {g : b ≤ c} {h : c ≤ d} 
          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc {a} {b} {c} {d} {f} {g} {h} = proof-irr-≤ a d (ptrans (ptrans f g) h) (ptrans f (ptrans g h))
    
    right-id : {a b : Preorder.Carrier P} {f : a ≤ b} → id ∘ f ≡ f
    right-id {a} {b} {f} = proof-irr-≤ a b (ptrans f id) f

    left-id : {a b : Preorder.Carrier P} {f : a ≤ b} → f ∘ id ≡ f
    left-id {a} {b} {f} = proof-irr-≤ a b (ptrans id f) f

-------------------------------------------------------------------------------
-- The Binary Category
-------------------------------------------------------------------------------

binaryCategory : Category {zero} {zero}
binaryCategory = record
  { Obj = Bool
  ; Hom = Hom
  ; _∘_ = λ {a} {b} {c} → comp {a} {b} {c}
  ; id = λ {a} → id {a}
  ; assoc = λ {a} {b} {c} {d} {f} {g} {h} → assoc {a} {b} {c} {d} {f} {g} {h}
  ; left-id = λ {a} {b} {f} → left-id {a} {b} {f}
  ; right-id = λ {a} {b} {f} → right-id {a} {b} {f}
  } where
    Hom : Bool → Bool → Set zero
    Hom true  true  = ⊤
    Hom false true  = ⊤
    Hom false false = ⊤
    Hom _ _ = ⊥

    comp : {a b c : Bool} → Hom b c → Hom a b → Hom a c
    comp {true}  {true}  {true}  f g = tt
    comp {true}  {true}  {false} () g
    comp {true}  {false} {true}  f g = tt
    comp {true}  {false} {false} f ()
    comp {false} {true}  {true}  f g = tt
    comp {false} {true}  {false} f g = tt
    comp {false} {false} {true}  f g = tt
    comp {false} {false} {false} f g = tt

    id : {a : Bool} → Hom a a
    id {true}  = tt
    id {false} = tt
    
    assoc : {a b c d : Bool} {f : Hom a b} {g : Hom b c} {h : Hom c d} 
          → comp {a} {c} {d} h (comp {a} {b} {c} g f) ≡ comp {a} {b} {d} (comp {b} {c} {d} h g) f
    assoc {true}  {true}  {true}  {true}  {tt} {tt} {tt} = refl
    assoc {true}  {true}  {true}  {false} {tt} {tt} {()}
    assoc {true}  {true}  {false} {d}     {tt} {()} {h}
    assoc {true}  {false} {c}     {d}     {()} {g}  {h}
    assoc {false} {true}  {true}  {true}  {tt} {tt} {tt} = refl
    assoc {false} {true}  {true}  {false} {tt} {tt} {()}
    assoc {false} {true}  {false} {d}     {tt} {()} {h}
    assoc {false} {false} {true}  {true}  {tt} {tt} {tt} = refl
    assoc {false} {false} {true}  {false} {tt} {tt} {()}
    assoc {false} {false} {false} {true}  {tt} {tt} {tt} = refl
    assoc {false} {false} {false} {false} {tt} {tt} {tt} = refl

    right-id : {a b : Bool} {f : Hom a b} → comp {a} {b} {b} (id {b}) f ≡ f
    right-id {true} {true} {tt} = refl
    right-id {true} {false} {()}
    right-id {false} {true} {tt} = refl
    right-id {false} {false} {tt} = refl

    left-id : {a b : Bool} {f : Hom a b} → comp {a} {a} {b} f (id {a}) ≡ f
    left-id {true} {true} {tt} = refl
    left-id {true} {false} {()}
    left-id {false} {true} {tt} = refl
    left-id {false} {false} {tt} = refl
