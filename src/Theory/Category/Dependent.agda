
open import Level

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; ≡-to-≅ ; ≅-to-≡ )

open import Equality
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor

module Theory.Category.Dependent where

record DependentCategory {ℓ₀ ℓ₁ ℓDep₀ ℓDep₁ : Level} (C : Category {ℓ₀} {ℓ₁}) : Set (ℓ₀ ⊔ ℓ₁ ⊔ suc (ℓDep₀ ⊔ ℓDep₁)) where
  constructor dependentCategory
  open Category C
  
  field
    DepObj : Obj → Set ℓDep₀
    
    DepHom : {a b : Obj} → DepObj a → DepObj b → Hom a b → Set ℓDep₁
    
    _∘dep_ : {a b c : Obj} {f : Hom b c} {g : Hom a b} 
           → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c}
           → DepHom b' c' f → DepHom a' b' g → DepHom a' c' (f ∘ g)
    
    depId : {a : Obj} {a' : DepObj a} → DepHom a' a' (id {a})
    
    dep-assoc : {a b c d : Obj}
              → {f : Hom a b} {g : Hom b c} {h : Hom c d}
              → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d}
              → (f' : DepHom a' b' f) → (g' : DepHom b' c' g) → (h' : DepHom c' d' h) 
              → h' ∘dep (g' ∘dep f') ≅ (h' ∘dep g') ∘dep f'

    dep-right-id : {a b : Obj} {f : Hom a b} 
                 → {a' : DepObj a} {b' : DepObj b}
                 → (f' : DepHom a' b' f)
                 → depId {b} {b'} ∘dep f' ≅ f'

    dep-left-id : {a b : Obj} {f : Hom a b}
                → {a' : DepObj a} {b' : DepObj b}
                → (f' : DepHom a' b' f)
                → f' ∘dep depId {a} {a'} ≅ f'
  
  DepCat : Category {ℓ₀ ⊔ ℓDep₀} {ℓ₁ ⊔ ℓDep₁}
  DepCat = record
    { Obj = Σ Obj DepObj
    ; Hom = Hom'
    ; _∘_ = _∘'_
    ; id = id , depId
    ; assoc = λ {a} {b} {c} {d} {f} {g} {h} 
            → Σ-eq (assoc {f = proj₁ f} {proj₁ g} {proj₁ h}) (dep-assoc (proj₂ f) (proj₂ g) (proj₂ h))
    ; left-id  = λ {a} {b} {f} 
               → Σ-eq (left-id  {f = proj₁ f}) (dep-left-id  (proj₂ f))
    ; right-id = λ {a} {b} {f} 
               → Σ-eq (right-id {f = proj₁ f}) (dep-right-id (proj₂ f))
    } where
      Hom' : Σ Obj DepObj → Σ Obj DepObj → Set (ℓ₁ ⊔ ℓDep₁)
      Hom' (a , a') (b , b') = Σ (Hom a b) (DepHom a' b')

      _∘'_ : {a b c : Σ Obj DepObj} → Hom' b c → Hom' a b → Hom' a c
      _∘'_ (f , f') (g , g') = f ∘ g , f' ∘dep g'
  
  forgetful-functor : Functor DepCat C
  forgetful-functor = functor proj₁ proj₁ refl refl

open Category

private
  module Properties {ℓ₀ ℓ₁ ℓDep₀ ℓDep₁ : Level} {C : Category {ℓ₀} {ℓ₁}} (DC : DependentCategory {ℓDep₀ = ℓDep₀} {ℓDep₁} C) where
    open DependentCategory hiding ( DepCat )
    
    private
      DepCat = DependentCategory.DepCat DC

    DependentObjUniqueness : Set (ℓDep₀ ⊔ ℓ₀)
    DependentObjUniqueness = (a b : Σ (Obj C) (DepObj DC)) → proj₁ a ≡ proj₁ b → proj₂ a ≅ proj₂ b
    
    DependentHomUniqueness : Set (ℓDep₁ ⊔ ℓDep₀ ⊔ ℓ₁ ⊔ ℓ₀)
    DependentHomUniqueness = {a b : Obj DepCat} → (f g : Hom DepCat a b) → proj₁ f ≡ proj₁ g → proj₂ f ≅ proj₂ g
  
    forgetful-functor-faithful : DependentHomUniqueness → IsFaithfulFunctor (forgetful-functor DC)
    forgetful-functor-faithful dep-hom-unique a b (f₁ , f₂) (.f₁ , g₂) refl = cong (_,_ f₁) (≅-to-≡ (dep-hom-unique (f₁ , f₂) (f₁ , g₂) refl))

open Properties public

open import Function hiding ( id ; _∘_ )

productDependentCategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                         → (C : Category {ℓC₀} {ℓC₁}) (D : Category {ℓD₀} {ℓD₁})
                         → DependentCategory {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} C
productDependentCategory C D = dependentCategory (const $ Obj D) (λ a b → const $ Hom D a b) (_∘_ D) (id D) 
                                                 (λ f' g' h' → ≡-to-≅ (assoc D {f = f'} {g'} {h'})) 
                                                 (λ f' → ≡-to-≅ (right-id D)) 
                                                 (λ f' → ≡-to-≅ (left-id D))

