
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

  field

    _Dep⊗₀_ : {a b : Obj C} → DepObj a → DepObj b → DepObj (a ⊗₀ b)

    _Dep⊗₁_ : {a b c d : Obj C}
            → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d}
            → {f : Hom C a b} {g : Hom C c d}
            → (f' : DepHom a' b' f) (g' : DepHom c' d' g)
            → DepHom (a' Dep⊗₀ c') (b' Dep⊗₀ d') (f ⊗₁ g)

    depUnit : DepObj unit

    dep-tensor-id : {a b : Obj C} {a' : DepObj a} {b' : DepObj b} → depId {a} {a'} Dep⊗₁ depId {b} {b'} ≅ depId {a ⊗₀ b} {a' Dep⊗₀ b'}

    dep-tensor-compose : {a b c d e i : Obj C}
                       → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d} {e' : DepObj e} {i' : DepObj i}
                       → {f : Hom C a c} {g : Hom C b d} {h : Hom C c e} {k : Hom C d i}
                       → {f' : DepHom a' c' f} {g' : DepHom b' d' g} {h' : DepHom c' e' h} {k' : DepHom d' i' k}
                       → (h' ∘dep f') Dep⊗₁ (k' ∘dep g') ≅ (h' Dep⊗₁ k') ∘dep (f' Dep⊗₁ g')

    dep-α : {x y z : Obj C}
          → (x' : DepObj x) (y' : DepObj y) (z' : DepObj z)
          → DepHom ((x' Dep⊗₀ y') Dep⊗₀ z') (x' Dep⊗₀ (y' Dep⊗₀ z')) (α x y z)
    
    dep-α-inv : {x y z : Obj C}
              → (x' : DepObj x) (y' : DepObj y) (z' : DepObj z)
              → DepHom  (x' Dep⊗₀ (y' Dep⊗₀ z')) ((x' Dep⊗₀ y') Dep⊗₀ z') (α-inv MC x y z)
    
    dep-λ : {x : Obj C} (x' : DepObj x)
          → DepHom (depUnit Dep⊗₀ x') x' (λ' x)
    
    dep-λ-inv : {x : Obj C} (x' : DepObj x)
              → DepHom x' (depUnit Dep⊗₀ x') (λ-inv MC x)

    dep-ρ : {x : Obj C} (x' : DepObj x)
          → DepHom (x' Dep⊗₀ depUnit) x' (ρ x)
    
    dep-ρ-inv : {x : Obj C} (x' : DepObj x)
              → DepHom x' (x' Dep⊗₀ depUnit) (ρ-inv MC x)

    
    dep-α-natural : {a b c d e i : Obj C} 
                  → {a' : DepObj a} {b' : DepObj b} {c' : DepObj c} {d' : DepObj d} {e' : DepObj e} {i' : DepObj i}
                  → {f : Hom C a d} {g : Hom C b e} {h : Hom C c i}
                  → {f' : DepHom a' d' f} {g' : DepHom b' e' g} {h' : DepHom c' i' h}
                  → (f' Dep⊗₁ (g' Dep⊗₁ h')) ∘dep dep-α a' b' c' ≅ dep-α d' e' i' ∘dep ((f' Dep⊗₁ g') Dep⊗₁ h')
    
    dep-λ-natural : {a b : Obj C} {a' : DepObj a} {b' : DepObj b}
                  → {f : Hom C a b} {f' : DepHom a' b' f}
                  → f' ∘dep dep-λ a' ≅ dep-λ b' ∘dep (depId Dep⊗₁ f')

    dep-ρ-natural : {a b : Obj C} {a' : DepObj a} {b' : DepObj b}
                  → {f : Hom C a b} {f' : DepHom a' b' f}
                  → f' ∘dep dep-ρ a' ≅ dep-ρ b' ∘dep (f' Dep⊗₁ depId)
    
    dep-α-left-id : {a b c : Obj C} 
                  → (a' : DepObj a) (b' : DepObj b) (c' : DepObj c)
                  → dep-α a' b' c' ∘dep dep-α-inv a' b' c' ≅ depId {a' = a' Dep⊗₀ (b' Dep⊗₀ c')}
    
    dep-α-right-id : {a b c : Obj C} 
                   → (a' : DepObj a) (b' : DepObj b) (c' : DepObj c)
                   → dep-α-inv a' b' c' ∘dep dep-α a' b' c' ≅ depId {a' = (a' Dep⊗₀ b') Dep⊗₀ c'}

    dep-λ-left-id : {a : Obj C} → (a' : DepObj a)
                  → dep-λ a' ∘dep dep-λ-inv a' ≅ depId {a' = a'}
    
    dep-λ-right-id : {a : Obj C} → (a' : DepObj a)
                   → dep-λ-inv a' ∘dep dep-λ a'  ≅ depId {a' = depUnit Dep⊗₀ a'}

    dep-ρ-left-id : {a : Obj C} → (a' : DepObj a)
                  → dep-ρ a' ∘dep dep-ρ-inv a' ≅ depId {a' = a'}
    
    dep-ρ-right-id : {a : Obj C} → (a' : DepObj a)
                   → dep-ρ-inv a' ∘dep dep-ρ a'  ≅ depId {a' = a' Dep⊗₀ depUnit}
    
    dep-triangle-id : {x y : Obj C}
                    → (x' : DepObj x) (y' : DepObj y)
                    → _Dep⊗₁_ {c' = y'} (dep-ρ x') depId ≅ (depId Dep⊗₁ dep-λ y') ∘dep dep-α x' depUnit y'
    
    dep-pentagon-id : {w x y z : Obj C}
                    → (w' : DepObj w) (x' : DepObj x) (y' : DepObj y) (z' : DepObj z)
                    → (depId Dep⊗₁ dep-α x' y' z') ∘dep (dep-α w' (x' Dep⊗₀ y') z' ∘dep (dep-α w' x' y' Dep⊗₁ depId))
                    ≅ dep-α w' x' (y' Dep⊗₀ z') ∘dep (dep-α (w' Dep⊗₀ x') y' z')
    
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
    ; unit = unit , depUnit
    ; associator = record
      { natural-transformation = record
        { η = λ x → α (proj₁ (p₁ x)) (proj₁ (p₂ x)) (proj₁ (p₃ x)) 
                  , dep-α (proj₂ (p₁ x)) (proj₂ (p₂ x)) (proj₂ (p₃ x))
        ; natural = λ {a} {b} {f} → Σ-eq (α-natural {down-p₀ a} {down-p₀ b} {down-p₁ f}) 
                                         (dep-α-natural {a' = proj₂ (p₁ a)} {proj₂ (p₂ a)} {proj₂ (p₃ a)} {proj₂ (p₁ b)} {proj₂ (p₂ b)} {proj₂ (p₃ b)} 
                                                        {f' = proj₂ (p₁ f)} {proj₂ (p₂ f)} {proj₂ (p₃ f)}) 
        }
      ; isomorphic = λ x → record
        { f⁻¹ = α-inv MC (proj₁ (p₁ x)) (proj₁ (p₂ x)) (proj₁ (p₃ x)) 
              , dep-α-inv (proj₂ (p₁ x)) (proj₂ (p₂ x)) (proj₂ (p₃ x))
        ; left-id  = Σ-eq (α-left-id  MC (proj₁ (p₁ x)) (proj₁ (p₂ x)) (proj₁ (p₃ x))) 
                          (dep-α-left-id (proj₂ (p₁ x)) (proj₂ (p₂ x)) (proj₂ (p₃ x)))
        ; right-id = Σ-eq (α-right-id MC (proj₁ (p₁ x)) (proj₁ (p₂ x)) (proj₁ (p₃ x))) 
                          (dep-α-right-id (proj₂ (p₁ x)) (proj₂ (p₂ x)) (proj₂ (p₃ x)))
        }
      }
    ; left-unitor = record
      { natural-transformation = record
        { η = λ x → λ' (proj₁ x) , dep-λ (proj₂ x)
        ; natural = λ {a} {b} {f} → Σ-eq (λ-natural {proj₁ a} {proj₁ b} {proj₁ f}) 
                                         (dep-λ-natural {a' = proj₂ a} {proj₂ b} {f' = proj₂ f})
        }
      ; isomorphic = λ x → record
        { f⁻¹ = λ-inv MC (proj₁ x) , dep-λ-inv (proj₂ x)
        ; left-id  = Σ-eq (λ-left-id MC (proj₁ x)) (dep-λ-left-id (proj₂ x))
        ; right-id = Σ-eq (λ-right-id MC (proj₁ x)) (dep-λ-right-id (proj₂ x))
        }
      }
    ; right-unitor = record
      { natural-transformation = record
        { η = λ x → ρ (proj₁ x) , dep-ρ (proj₂ x)
        ; natural = λ {a} {b} {f} → Σ-eq (ρ-natural {proj₁ a} {proj₁ b} {proj₁ f}) 
                                         (dep-ρ-natural {a' = proj₂ a} {proj₂ b} {f' = proj₂ f})
        }
      ; isomorphic = λ x → record
        { f⁻¹ = ρ-inv MC (proj₁ x) , dep-ρ-inv (proj₂ x)
        ; left-id  = Σ-eq (ρ-left-id MC (proj₁ x)) (dep-ρ-left-id (proj₂ x))
        ; right-id = Σ-eq (ρ-right-id MC (proj₁ x)) (dep-ρ-right-id (proj₂ x))
        }
      }
    ; triangle-id = λ x y → Σ-eq (triangle-id (proj₁ x) (proj₁ y)) 
                                 (dep-triangle-id (proj₂ x) (proj₂ y))
    ; pentagon-id = λ w x y z → Σ-eq (pentagon-id (proj₁ w) (proj₁ x) (proj₁ y) (proj₁ z)) 
                                     (dep-pentagon-id (proj₂ w) (proj₂ x) (proj₂ y) (proj₂ z))
    }
