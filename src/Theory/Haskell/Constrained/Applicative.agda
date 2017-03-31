
open import Level
open import Function renaming ( id to idF ;  _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality

open import Theory.Category
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Dependent
open import Theory.Category.Examples

open import Theory.Functor
open import Theory.Functor.Monoidal

open import Theory.Natural.Transformation

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Applicative {ℓ : Level} where

private
  Hask = setCategory {ℓ}
  HaskMon = setMonoidalCategory {ℓ}
  Type = Set ℓ
  _∘Hask_ = Category._∘_ Hask

open import Theory.Functor.Composition
record ConstrainedApplicative {ℓCt₀ ℓCt₁ : Level} (MCC : MonoidalConstraintCategory {ℓ} {ℓCt₀} {ℓCt₁}) : Set (suc (ℓ ⊔ ℓCt₀ ⊔ ℓCt₁)) where
  open Category
  open MonoidalCategory hiding ( Obj ; Hom ; _⊗₀_ ; _⊗₁_ ; unit ) 
  open ConstrainedFunctor hiding ( Cts ; CtFunctor ; map )
  
  Cts = MCC
  
  field
    CtsFunctor : ConstrainedFunctor (DependentMonoidalCategory.DC Cts)
  
  CtCategory : Category
  CtCategory = DependentMonoidalCategory.DepCat Cts
  
  CtMonoidalCategory : MonoidalCategory CtCategory 
  CtMonoidalCategory = DependentMonoidalCategory.DepMonCat Cts
  
  CtFunctor : Functor CtCategory Hask
  CtFunctor = ConstrainedFunctor.CtFunctor CtsFunctor
  
  open Functor CtFunctor using ( F₀ ; F₁ )
  open MonoidalCategory CtMonoidalCategory using ( _⊗₀_ ; _⊗₁_ ) renaming ( unit to unit-mc )
  
  field
    unit : F₀ unit-mc
    
    prod-map : (x y : Obj CtCategory) → (F₀ x) × (F₀ y) → F₀ (x ⊗₀ y)
    
    naturality : {a a' b b' : Obj CtCategory} {f : Category.Hom CtCategory a b} {f' : Category.Hom CtCategory a' b'}
               → F₁ (f ⊗₁ f') ∘F prod-map a a' ≡ prod-map b b' ∘F (λ x → (F₁ f (proj₁ x) , F₁ f' (proj₂ x)))
    
    associativity : (x y z : Obj CtCategory) 
                  → F₁ (α CtMonoidalCategory x y z) ∘F (prod-map (x ⊗₀ y) z ∘F (λ a → prod-map x y (proj₁ a) , proj₂ a))
                  ≡ prod-map x (y ⊗₀ z) ∘F ((λ a → proj₁ a , prod-map y z (proj₂ a)) ∘F (α HaskMon (F₀ x) (F₀ y) (F₀ z)))
    
    left-unitality : (x : Obj CtCategory) → λ' HaskMon (F₀ x) ≡ F₁ (λ' CtMonoidalCategory x) ∘F (prod-map unit-mc x ∘F (λ a → unit , proj₂ a))

    right-unitality : (x : Obj CtCategory) → ρ HaskMon (F₀ x) ≡ F₁ (ρ  CtMonoidalCategory x) ∘F (prod-map x unit-mc ∘F (λ a → proj₁ a , unit))
    
  map = ConstrainedFunctor.map CtsFunctor

  CtApplicative : LaxMonoidalFunctor CtMonoidalCategory HaskMon
  CtApplicative = record 
    { F = CtFunctor
    ; ε = λ _ → unit
    ; μ-natural-transformation = record
      { η = λ x → prod-map (proj₁ x) (proj₂ x)
      ; natural = λ {a} {b} {f} → naturality {proj₁ a} {proj₂ a} {proj₁ b} {proj₂ b} {proj₁ f} {proj₂ f}
      }
    ; assoc = associativity
    ; left-unitality = left-unitality
    ; right-unitality = right-unitality
    }
  {-
  pure : (A : Obj CtCategory)  → (proj₁ A  → F₀ A)
  pure (A , CtA) a = map ((λ _ → a) , {!!}) unit
  -}
