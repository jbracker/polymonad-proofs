
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Equality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category
open import Theory.Category.Monoidal
open import Theory.Category.Dependent
open import Theory.Category.Isomorphism

open import Theory.Functor

open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Dependent where

record DependentMonoidalCategory {ℓ₀ ℓ₁ ℓDep₀ ℓDep₁ : Level} {C : Category {ℓ₀} {ℓ₁}} (MC : MonoidalCategory C) : Set (ℓ₀ ⊔ ℓ₁ ⊔ suc (ℓDep₀ ⊔ ℓDep₁)) where

  field
    DC : DependentCategory {ℓDep₀ = ℓDep₀} {ℓDep₁} C

  open DependentCategory DC public
  open MonoidalCategory MC hiding ( _∘_ ; Obj ; Hom ; id )
  open Category

  private
    _∘C_ = _∘_ C
    _∘DC_ = _∘_ DepCat
    _∘DC×DC_ = _∘_ (DepCat ×C DepCat)
    _∘DC×DC×DC_ = _∘_ (DepCat ×C DepCat ×C DepCat)
    _∘DC×[DC×DC]_ = _∘_ (DepCat ×C (DepCat ×C DepCat))
    _∘[DC×DC]×DC_ = _∘_ ((DepCat ×C DepCat) ×C DepCat)

  field

    _Dep⊗₀_ : {a b : Obj C} → DepObj a → DepObj b → DepObj (a ⊗₀ b)

    _Dep⊗₁_ : {a b c d : Obj C}
            → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d}
            → {f : Hom C a b} {g : Hom C c d}
            → (f' : DepHom a' b' f) (g' : DepHom c' d' g)
            → DepHom (a' Dep⊗₀ c') (b' Dep⊗₀ d') (f ⊗₁ g)

    depUnit : Obj DepCat

    dep-tensor-id : {a b : Obj C} {a' : DepObj a} {b' : DepObj b} → depId {a} {a'} Dep⊗₁ depId {b} {b'} ≅ depId {a ⊗₀ b} {a' Dep⊗₀ b'}

    dep-tensor-compose : {a b c d e i : Obj C}
                       → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d} {e' : DepObj e} {i' : DepObj i}
                       → {f : Hom C a c} {g : Hom C b d} {h : Hom C c e} {k : Hom C d i}
                       → {f' : DepHom a' c' f} {g' : DepHom b' d' g} {h' : DepHom c' e' h} {k' : DepHom d' i' k}
                       → (h' ∘dep f') Dep⊗₁ (k' ∘dep g') ≅ (h' Dep⊗₁ k') ∘dep (f' Dep⊗₁ g') -- f' Dep⊗₁ proj₂ (proj₂ (g ∘DC×DC f)) ≅ f' ∘dep g'

    dep-α : {x y z : Obj C} {x' : DepObj x} {y' : DepObj y} {z' : DepObj z}
          → DepHom ((x' Dep⊗₀ y') Dep⊗₀ z') (x' Dep⊗₀ (y' Dep⊗₀ z')) (α x y z)

    dep-λ : {x : Obj C} {x' : DepObj x}
          → Hom DepCat (proj₁ depUnit ⊗₀ x , proj₂ depUnit Dep⊗₀ x') (x , x')

    dep-ρ : {x : Obj C} {x' : DepObj x}
          → Hom DepCat (x ⊗₀ proj₁ depUnit , x' Dep⊗₀ proj₂ depUnit) (x , x')

    
    dep-α-natural : {a b c d e i : Obj C} 
                  → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d} {e' : DepObj e} {i' : DepObj i}
                  → {f : Hom C a d} {g : Hom C b e} {h : Hom C c i}
                  → {f' : DepHom a' d' f} {g' : DepHom b' e' g} {h' : DepHom c' i' h}
                  → (f' Dep⊗₁ (g' Dep⊗₁ h')) ∘dep dep-α ≅ dep-α ∘dep ((f' Dep⊗₁ g') Dep⊗₁ h')

  private
    down-proj₀ : Obj (DepCat ×C DepCat) → Obj (C ×C C)
    down-proj₀ ((a , a') , (b , b')) = a , b 
    
    down-proj₁ : {a b : Obj (DepCat ×C DepCat)} → Hom (DepCat ×C DepCat) a b → Hom (C ×C C) (down-proj₀ a) (down-proj₀ b)
    down-proj₁ ((f , f') , (g , g')) = f , g
    
    down-p₀ : Obj (DepCat ×C DepCat ×C DepCat) → Obj (C ×C C ×C C)
    down-p₀ ((a , _) ,' (b , _) ,' (c , _)) = a ,' b ,' c
    
    down-p₁ : {a b : Obj (DepCat ×C DepCat ×C DepCat)} → Hom (DepCat ×C DepCat ×C DepCat) a b → Hom (C ×C C ×C C) (down-p₀ a) (down-p₀ b)
    down-p₁ ((f , _) ,' (g , _) ,' (h , _)) = f ,' g ,' h
    

  DepTensor : Functor (DepCat ×C DepCat) DepCat
  DepTensor = record
    { F₀ = λ a → (proj₁ (proj₁ a) ⊗₀ proj₁ (proj₂ a)) , (proj₂ (proj₁ a) Dep⊗₀ proj₂ (proj₂ a))
    ; F₁ = λ f → (proj₁ (proj₁ f) ⊗₁ proj₁ (proj₂ f)) , (proj₂ (proj₁ f) Dep⊗₁ proj₂ (proj₂ f))
    ; id = λ {a} → Σ-eq (Functor.id tensor {down-proj₀ a}) 
                        (dep-tensor-id {proj₁ (proj₁ a)} {proj₁ (proj₂ a)} {proj₂ (proj₁ a)} {proj₂ (proj₂ a)})
    ; compose = λ {a} {b} {c} {f} {g} → Σ-eq (Functor.compose tensor {down-proj₀ a} {down-proj₀ b} {down-proj₀ c} {down-proj₁ f} {down-proj₁ g}) 
                                             (dep-tensor-compose {a' = proj₂ (proj₁ a)} {proj₂ (proj₂ a)} {proj₂ (proj₁ b)} {proj₂ (proj₂ b)} {proj₂ (proj₁ c)} {proj₂ (proj₂ c)} 
                                                                 {f' = proj₂ (proj₁ f)} {proj₂ (proj₂ f)} {proj₂ (proj₁ g)} {proj₂ (proj₂ g)})
    }
  
  open Triple renaming ( proj₁ to p₁ ; proj₂ to p₂ ; proj₃ to p₃ )
  
  DepMonCat : MonoidalCategory DepCat
  DepMonCat = record
    { tensor = DepTensor
    ; unit = depUnit
    ; associator = record
      { natural-transformation = record
        { η = λ x → α (proj₁ (p₁ x)) (proj₁ (p₂ x)) (proj₁ (p₃ x)) 
                  , dep-α {proj₁ (p₁ x)} {proj₁ (p₂ x)} {proj₁ (p₃ x)} {proj₂ (p₁ x)} {proj₂ (p₂ x)} {proj₂ (p₃ x)}
        ; natural = λ {a} {b} {f} → Σ-eq (α-natural {down-p₀ a} {down-p₀ b} {down-p₁ f}) 
                                         (dep-α-natural {a' = proj₂ (p₁ a)} {proj₂ (p₂ a)} {proj₂ (p₃ a)} {proj₂ (p₁ b)} {proj₂ (p₂ b)} {proj₂ (p₃ b)} 
                                                        {f' = proj₂ (p₁ f)} {proj₂ (p₂ f)} {proj₂ (p₃ f)}) 
        }
      ; isomorphic = {!!}
      }
    ; left-unitor = record
      { natural-transformation = record
        { η = λ x → dep-λ {proj₁ x} {proj₂ x}
        ; natural = λ {a} {b} {f} → Σ-eq {!!} {!!}
        }
      ; isomorphic = {!!}
      }
    ; right-unitor = record
      { natural-transformation = record
        { η = λ x → dep-ρ {proj₁ x} {proj₂ x}
        ; natural = λ {a} {b} {f} → Σ-eq {!!} {!!}
        }
      ; isomorphic = {!!}
      }
    ; triangle-id = {!!}
    ; pentagon-id = {!!}
    } where
  {-
      import Theory.Functor.Association
      open Theory.Functor.Association.Associator
      import Theory.Functor.Application
      open Theory.Functor.Application.BiFunctor
    -}  
