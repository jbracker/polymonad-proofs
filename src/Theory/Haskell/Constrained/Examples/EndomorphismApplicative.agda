 
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( trans )
open ≡-Reasoning

open import Extensionality
open import Equality
open import Congruence
open import ProofIrrelevance

open import Theory.Category
open import Theory.Category.Isomorphism
open import Theory.Category.Concrete
open import Theory.Category.Dependent
open import Theory.Category.Examples
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples
open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor

module Theory.Haskell.Constrained.Examples.EndomorphismApplicative {ℓ : Level} where

open import Theory.Haskell.Constrained.Examples.EndomorphismFunctor {ℓ}

private
  Type = Set ℓ
  Hask = setCategory {ℓ}
  CCE = ConstraintCategoryEndomorphisms

open Category
open DependentCategory
open Isomorphism

private
  _∘×_ : {a b c d : Type} → (f : a → b) (g : c → d) → (a × c) → (b × d)
  _∘×_ f g (a , c) = f a , g c
  
  _Dep⊗₁_ : {a b c d : Type} {f : a → b} {g : c → d} → Isomorphism Hask f → Isomorphism Hask g → Isomorphism Hask (f ∘× g)
  _Dep⊗₁_ {a} {b} {c} {d} {f} {g} iso-f iso-g = isomorphism (inv iso-f ∘× inv iso-g) (fun-ext left-id') (fun-ext right-id')
    where
      left-id' : (x : b × d) → ((f ∘× g) ∘F (inv iso-f ∘× inv iso-g)) x ≡ id Hask x
      left-id' x = {!!}
      
      right-id' : (x : a × c) → ((inv iso-f ∘× inv iso-g) ∘F (f ∘× g)) x ≡ id Hask x
      right-id' x = {!!}

  {-
  tensor-compose : {a b c d e i : Type} (f' : a ≡ c) (g' : b ≡ d) (h' : c ≡ e) (k' : d ≡ i)
                 → (trans f' h') Dep⊗₁ (trans g' k') ≅ trans (f' Dep⊗₁ g') (h' Dep⊗₁ k') 
  tensor-compose refl refl refl refl = refl
  
  dep-α : (x y z : Type) → ((x × y) × z) ≡ (x × (y × z)) -- DepHom ConstraintCategoryEndomorphisms (lift tt) (lift tt) (MonoidalCategory.α setMonoidalCategory x y z)
  dep-α x y z = {!!}
  -}
MonoidalConstraintCategoryEndomorphisms : MonoidalConstraintCategory {ℓ} {ℓ}
MonoidalConstraintCategoryEndomorphisms = record
  { DC = ConstraintCategoryEndomorphisms
  ; _Dep⊗₀_ = λ _ _ → lift tt
  ; _Dep⊗₁_ = λ {a} {b} {c} {d} {a'} {b'} {c'} {d'} {f} {g} f' g' → _Dep⊗₁_ {f = f} {g} f' g'
  ; depUnit = {!!} -- lift tt
  ; dep-tensor-id = {!!} -- refl
  ; dep-tensor-compose = {!!} -- λ {a} {b} {c} {d} {e} {i} {a'} {b'} {c'} {d'} {e'} {i'} {f} {g} {h} {k} {f'} {g'} {h'} {k'} → tensor-compose f' g' h' k'
  ; dep-α = {!!} -- λ {x} {y} {z} x' y' z' → dep-α x y z
  ; dep-α-inv = {!!}
  ; dep-λ = {!!}
  ; dep-λ-inv = {!!}
  ; dep-ρ = {!!}
  ; dep-ρ-inv = {!!}
  ; dep-α-natural = {!!}
  ; dep-λ-natural = {!!}
  ; dep-ρ-natural = {!!}
  ; dep-α-left-id = {!!}
  ; dep-α-right-id = {!!}
  ; dep-λ-left-id = {!!}
  ; dep-λ-right-id = {!!}
  ; dep-ρ-left-id = {!!}
  ; dep-ρ-right-id = {!!}
  ; dep-triangle-id = {!!}
  ; dep-pentagon-id = {!!}
  }
