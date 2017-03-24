
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( trans )
open ≡-Reasoning

open import Extensionality
open import Congruence
open import ProofIrrelevance

open import Theory.Category
open import Theory.Category.Concrete
open import Theory.Category.Dependent
open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Examples.EndomorphismFunctor {ℓ : Level} where

private
  Type = Set ℓ

-- The functor of endomorphisms.
data Endo (α : Type) : Type where
  endo : (α → α) → Endo α

-- fmap of the functor of endomorphisms.
endomap : {α : Type} → (α → α) → (Endo α) → (Endo α)
endomap f (endo g) = endo $ f ∘F g

ConstraintCategoryEndomorphisms : ConstraintCategory {ℓ}
ConstraintCategoryEndomorphisms 
  = dependentCategory ObjCts HomCts (flip trans) refl 
                      (λ {α} {β} {γ} {δ} {f} {g} {h} {α'} {β'} {γ'} {δ'} f' g' h' → ≡-to-≅ $ assoc {f = f} {g} {h} f' g' h')
                      (λ {α} {β} {f} {α'} {β'} f' → ≡-to-≅ $ right-id {f = f} f') 
                      (λ {α} {β} {f} {α'} {β'} f' → ≡-to-≅ $ left-id {f = f} f')
  where
    ObjCts : Type → Set ℓ
    ObjCts _ = Lift ⊤
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set (lsuc ℓ)
    HomCts = λ {α} {β} _ _ _ → α ≡ β
    
    assoc : {α β γ δ : Type} 
          → {f : α → β} {g : β → γ} {h : γ → δ}
          → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
          → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h) 
          → flip trans h' (flip trans g' f') ≡ flip trans (flip trans h' g') f'
    assoc refl refl refl = refl
    
    right-id : {α β : Type} {f : α → β} {α' : ObjCts α} {β' : ObjCts β} 
             → (f' : HomCts α' β' f) → flip trans refl f' ≡ f'
    right-id refl = refl
    
    left-id : {α β : Type} {f : α → β} {α' : ObjCts α} {β' : ObjCts β}
            → (f' : HomCts α' β' f) → flip trans f' refl ≡ f'
    left-id refl = refl

-- The categorical structure of the constrained functor.
FunctorEndomorphisms : ConstrainedFunctor ConstraintCategoryEndomorphisms
FunctorEndomorphisms = record
  { F = F
  ; map = map
  ; functor-id = functor-id
  ; functor-compose = λ {α} {β} {γ} {f} {g} → functor-compose {α} {β} {γ} {f} {g}
  } where
    Cts : ConstraintCategory {ℓ}
    Cts = ConstraintCategoryEndomorphisms
    
    open DependentCategory Cts
    open Category DepCat
    
    F : Obj → Type
    F α = Endo (proj₁ α)
    
    map : {α β : Obj} → (Hom α β) → F α → F β
    map (f , refl) x = endomap f x
    
    functor-id : {α : Obj} → endomap {α = proj₁ α} idF ≡ idF
    functor-id {α , lift tt} = fun-ext helper
      where helper : (x : Endo α) → endomap idF x ≡ idF x
            helper (endo f) = refl
    
    functor-compose : {α β γ : Obj} {f : Hom α β} {g : Hom β γ}
                    → map (proj₁ g ∘F proj₁ f , flip trans (proj₂ g) (proj₂ f)) ≡ map g ∘F map f
    functor-compose {α , lift tt} {.α , lift tt} {.α , lift tt} {f , refl} {g , refl} = fun-ext helper
      where helper : (x : Endo α) → endomap (g ∘F f) x ≡ (endomap g ∘F endomap f) x
            helper (endo h) = refl

FunctorEndomorphisms-DependentHomUniqueness : DependentHomUniqueness (ConstrainedFunctor.Cts FunctorEndomorphisms)
FunctorEndomorphisms-DependentHomUniqueness (f₁ , refl) (.f₁ , refl) refl = refl

FunctorEndomorphisms-DependentObjUniqueness : DependentObjUniqueness (ConstrainedFunctor.Cts FunctorEndomorphisms)
FunctorEndomorphisms-DependentObjUniqueness (a₁ , lift tt) (.a₁ , lift tt) refl = refl
 
FunctorEndomorphisms-UniqueInstances : UniqueInstances (ConstrainedFunctor.Cts FunctorEndomorphisms)
FunctorEndomorphisms-UniqueInstances = unique-type-inst , unique-hom-inst
  where
    open DependentCategory (ConstrainedFunctor.Cts FunctorEndomorphisms)
    open Category DepCat
    
    unique-type-inst : (α : Type) → (αCts αCts' : DepObj α) → αCts ≡ αCts'
    unique-type-inst α (lift tt) (lift tt) = refl
    
    unique-hom-inst : {α β : Type} → (f g : α → β)
                    → (αCt : DepObj α) → (βCt : DepObj β) 
                    → (fCt : DepHom αCt βCt f) → (gCt : DepHom αCt βCt g)
                    → fCt ≅ gCt
    unique-hom-inst f g (lift tt) (lift tt) refl refl = refl

FunctorEndomorphismsCodomain-IsConcreteCategory : IsConcreteCategory (DependentCategory.DepCat (ConstrainedFunctor.Cts FunctorEndomorphisms))
FunctorEndomorphismsCodomain-IsConcreteCategory = ConstraintCategory→ConcreteCategory (ConstrainedFunctor.Cts FunctorEndomorphisms) FunctorEndomorphisms-DependentHomUniqueness
