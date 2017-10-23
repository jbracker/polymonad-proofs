
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )
open import Relation.Binary using ( Decidable ; IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open ≡-Reasoning

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell hiding ( Type )
open import Haskell.Applicative using ( _***_ )

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )

open import Theory.Functor.Definition

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Applicative

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Instances
open import Theory.Haskell.Constrained.Examples.SetFunctor.Product
open import Theory.Haskell.Constrained.Examples.SetFunctor.Map
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert
open import Theory.Haskell.Constrained.Examples.SetFunctor.Union
open import Theory.Haskell.Constrained.Examples.SetFunctor.Ap
open import Theory.Haskell.Constrained.Examples.SetFunctor

module Theory.Haskell.Constrained.Examples.SetApplicative {ℓ : Level} where 

open DependentCategory

open NotApplicativeReady

private
  SetMonCat' = SetMonCat {ℓ}
  SetCat' = SetCat {ℓ}

ObjTensor : {A B : Category.Obj SetCat'} 
          → DepObj ConstraintCategoryLSet A → DepObj ConstraintCategoryLSet B 
          → DepObj ConstraintCategoryLSet (A × B)
ObjTensor {A} {B} (OrdA , StructEqA) (OrdB , StructEqB) = OrdInstance-× OrdA OrdB , IsStructuralEquality-× OrdA OrdB StructEqA StructEqB

ConstraintMonoidalCategoryLSet : MonoidalConstraintCategory {ℓ} {suc ℓ}
ConstraintMonoidalCategoryLSet = record
  { DC = ConstraintCategoryLSet
  ; _Dep⊗₀_ = ObjTensor
  ; _Dep⊗₁_ = λ _ _ → tt
  ; depUnit = (Ord-⊤ , IsStructuralEquality-⊤)
  ; dep-tensor-id = refl
  ; dep-tensor-compose = refl
  ; dep-α = λ x' y' z' → tt
  ; dep-α-inv = λ x' y' z' → tt
  ; dep-λ = λ x' → tt
  ; dep-λ-inv = λ x' → tt
  ; dep-ρ = λ x' → tt
  ; dep-ρ-inv = λ x' → tt
  ; dep-α-natural = refl
  ; dep-λ-natural = refl
  ; dep-ρ-natural = refl
  ; dep-α-left-id = λ a' b' c' → refl
  ; dep-α-right-id = λ a' b' c' → refl
  ; dep-λ-left-id = λ a' → refl
  ; dep-λ-right-id = λ a' → refl
  ; dep-ρ-left-id = λ a' → refl
  ; dep-ρ-right-id = λ a' → refl
  ; dep-triangle-id = λ x' y' → refl
  ; dep-pentagon-id = λ w' x' y' z' → refl
  }


ApplicativeLSet : ConstrainedApplicative ConstraintMonoidalCategoryLSet
ApplicativeLSet = record
  { CtsFunctor = FunctorLSet
  ; unit = lset [] (lift tt)
  ; prod-map = ap'
  ; naturality = λ {a a' b b'} {f} {f'} → fun-ext (naturality {a} {a'} {b} {b'} {f} {f'})
  ; associativity = associativity
  ; left-unitality = left-unitality
  ; right-unitality = right-unitality
  } where
    open Functor (ConstrainedFunctor.CtFunctor FunctorLSet)
    open MonoidalCategory (DependentMonoidalCategory.DepMonCat ConstraintMonoidalCategoryLSet)

    set-α = MonoidalCategory.α SetMonCat'
    set-λ = MonoidalCategory.λ' SetMonCat'
    set-ρ = MonoidalCategory.ρ SetMonCat'
    
    tyOrd : Obj → Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})
    tyOrd (A , OrdA , StructEqA) = A , OrdA

    ty : Obj → Set ℓ
    ty (A , _) = A
    
    ord : (A : Obj) → OrdInstance {ℓ} {ℓ} {ℓ} (ty A)
    ord (_ , OrdA , _) = OrdA
    
    sEq : (A : Obj) → IsStructuralEquality (OrdInstance.eqInstance (ord A))
    sEq (_ , _ , StructEqA) = StructEqA
    
    ord-× : (A B : Obj) → OrdInstance {ℓ} {ℓ} {ℓ} (ty A × ty B)
    ord-× A B = OrdInstance-× (ord A) (ord B)
    
    sEq-× : (A B : Obj) → IsStructuralEquality (OrdInstance.eqInstance (ord-× A B))
    sEq-× A B = IsStructuralEquality-× (ord A) (ord B) (sEq A) (sEq B)

    tyOrd-× : Obj → Obj → Σ (Set ℓ) (OrdInstance {ℓ} {ℓ} {ℓ})
    tyOrd-× A B = (ty A × ty B) , (ord-× A B)
    
    ap' : (x y : Obj) → F₀ x × F₀ y → F₀ (x ⊗₀ y)
    ap' A B (sa , sb) = ap {A = tyOrd A} {tyOrd B} (sa , sb)
    
    all-× : Obj → Obj → Obj
    all-× A B = (ty A × ty B) , (ord-× A B) , sEq-× A B
    
    lset-× : Obj → Obj → Obj
    lset-× A B = LSet (tyOrd-× A B) , OrdLSet {A = tyOrd-× A B} , IsStructuralEquality-LSet (ord-× A B) (sEq-× A B)
    
    naturality : {a a' b b' : Obj}
               → {f : Hom a b} {f' : Hom a' b'}
               → (x : F₀ a × F₀ a')
               → (F₁ {a ⊗₀ a'} {b ⊗₀ b'} (_⊗₁_ {a} {b} {a'} {b'} f f') ∘F ap' a a') x
               ≡ (ap' b b' ∘F (λ x → F₁ {a} {b} f (proj₁ x) , F₁ {a'} {b'} f' (proj₂ x))) x
    naturality {a} {a'} {b} {b'} {f} {f'} (lset [] sorted , ys) = refl
    naturality {A} {A'} {B} {B'} {f , tt} {f' , tt} (lset (x ∷ xs) (sortedX , sortedXs) , ys) = begin
      (F₁ {A ⊗₀ A'} {B ⊗₀ B'} (_⊗₁_ {A} {B} {A'} {B'} (f , tt) (f' , tt)) ∘F ap' A A') (lset (x ∷ xs) (sortedX , sortedXs) , ys)
        ≡⟨ {!!} ⟩
      (ap' B B' ∘F (λ x → F₁ {A} {B} (f , tt) (proj₁ x) , F₁ {A'} {B'} (f' , tt) (proj₂ x))) (lset (x ∷ xs) (sortedX , sortedXs) , ys) ∎
    
    associativity : (x y z : Obj) 
                  → F₁ {(x ⊗₀ y) ⊗₀ z} {x ⊗₀ (y ⊗₀ z)} (α x y z) ∘F (ap' (x ⊗₀ y) z ∘F (λ a → ap' x y (proj₁ a) , proj₂ a))
                  ≡ ap' x (y ⊗₀ z) ∘F ((λ a → proj₁ a , ap' y z (proj₂ a)) ∘F set-α (F₀ x) (F₀ y) (F₀ z))
    associativity A B C = {!!}
    
    left-unitality : (x : Obj)
                   → set-λ (F₀ x)
                   ≡ F₁ {unit ⊗₀ x} {x} (λ' x) ∘F (ap' unit x ∘F (λ a → lset [] (lift tt) , proj₂ a))
    left-unitality A = {!!}
    
    right-unitality : (x : Obj) 
                    → set-ρ (F₀ x)
                    ≡ F₁ {x ⊗₀ unit} {x} (ρ x) ∘F (ap' x unit ∘F (λ a → proj₁ a , lset [] (lift tt)))
    right-unitality A = {!!}
