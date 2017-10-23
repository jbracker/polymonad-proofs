
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
open import Theory.Monad.Relative

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Applicative

open import Theory.Haskell.Constrained.Examples.LSet.Base
open import Theory.Haskell.Constrained.Examples.LSet.Instances
open import Theory.Haskell.Constrained.Examples.LSet.Product
open import Theory.Haskell.Constrained.Examples.LSet.Map
open import Theory.Haskell.Constrained.Examples.LSet.Insert
open import Theory.Haskell.Constrained.Examples.LSet.Union
open import Theory.Haskell.Constrained.Examples.LSet.KleisliExtension
open import Theory.Haskell.Constrained.Examples.SetFunctor

module Theory.Haskell.Constrained.Examples.SetMonad {ℓ : Level} where  

open NotApplicativeReady renaming ( FunctorLSet to CtFunctorLSet )

private
  FunctorLSet = ConstrainedFunctor.CtFunctor (CtFunctorLSet {ℓ})
  J = DependentCategory.forgetful-functor (ConstraintCategoryLSet {ℓ})

open Category
open Functor FunctorLSet renaming ( F₀ to LSet₀ ; F₁ to LSet₁ ; id to LSet-id ; compose to LSet-compose )

MonadLSet : RelativeMonad LSet₀ J
MonadLSet = record
  { η = λ {a} → η {a}
  ; kext = λ {a} {b} → kext {OrdA = ord a} {ord b}
  ; right-id = λ {A} {B} {k} → fun-ext (r-id {A} {B} k)
  ; left-id = λ {A} → fun-ext (l-id {A})
  ; coher = λ {A} {B} {C} {k} {l} → fun-ext (coher {A} {B} {C} k l)
  } where
    CtCatLSet : Category {suc ℓ} {ℓ}
    CtCatLSet = DependentCategory.DepCat (ConstraintCategoryLSet {ℓ})
    
    ty : Obj CtCatLSet → Set ℓ
    ty A = [ J ]₀ A
    
    ord : (A : Obj CtCatLSet) → OrdInstance {ℓ} {ℓ} {ℓ} (ty A)
    ord (A , OrdA , sEqA) = OrdA
    
    eq : (A : Obj CtCatLSet) → EqInstance {ℓ} {ℓ} (ty A)
    eq A = OrdInstance.eqInstance (ord A)
    
    sEq : (A : Obj CtCatLSet) → IsStructuralEquality (eq A)
    sEq (A , OrdA , sEqA) = sEqA

    η : {A : Obj CtCatLSet} 
      → [ J ]₀ A → LSet₀ A
    η {A} a = singleton (ty A , ord A) a

    abstract
      r-id : {A B : Obj CtCatLSet}
           → (k : [ J ]₀ A → LSet₀ B) 
           → (x : [ J ]₀ A)
           → (kext {OrdA = ord A} {ord B} k ∘F η {A}) x ≡ k x
      r-id k x with k x 
      r-id k x | lset [] _ = refl
      r-id k x | lset (kx ∷ kxs) (sortedKX , sortedKXs) = begin
        insertSet kx (union (lset kxs sortedKXs) (lset [] (lift tt)))
          ≡⟨ cong (insertSet kx) (union-with-empty (lset kxs sortedKXs)) ⟩ 
        insertSet kx (lset kxs sortedKXs)
          ≡⟨ insertSet-adds-in-front kx kxs (sortedKX , sortedKXs) ⟩ 
        lset (kx ∷ kxs) (sortedKX , sortedKXs) ∎
    
    abstract
      l-id : {A : Obj CtCatLSet}
           → (as : LSet₀ A)
           → kext {OrdA = ord A} {ord A} (η {A}) as ≡ as
      l-id {A} (lset [] _) = refl
      l-id {A} (lset (x ∷ xs) (sortedX , sortedXs)) = begin
           insertSet x (kext (η {A}) (lset xs sortedXs))
             ≡⟨ cong (insertSet x) (l-id {A = A} (lset xs sortedXs)) ⟩
           insertSet x (lset xs sortedXs)
             ≡⟨ insertSet-adds-in-front x xs (sortedX , sortedXs) ⟩
           lset (x ∷ xs) (sortedX , sortedXs) ∎
    
    abstract
      coher : {A B C : Obj CtCatLSet}
            → (k : [ J ]₀ A → LSet₀ B) 
            → (l : [ J ]₀ B → LSet₀ C)
            → (x : LSet₀ A)
            → (kext {OrdA = ord A} {ord C} (kext {OrdA = ord B} {ord C} l ∘F k)) x ≡ (kext {OrdA = ord B} {ord C} l ∘F kext {OrdA = ord A} {ord B} k) x
      coher k l (lset [] _) = refl
      coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) = begin
        union (kext l (k x)) (kext (kext l ∘F k) (lset xs sortedXs))
          ≡⟨ cong (λ X → union (kext l (k x)) X) (coher {A} {B} {C} k l (lset xs sortedXs)) ⟩
        union (kext l (k x)) ((kext l ∘F kext k) (lset xs sortedXs))
          ≡⟨ sym (kext-union-dist l (k x) (kext k (lset xs sortedXs)) (sEq B) (sEq C)) ⟩
        kext l (union (k x) (kext k (lset xs sortedXs)))
          ≡⟨ refl ⟩
        (kext l ∘F kext k) (lset (x ∷ xs) (sortedX , sortedXs)) ∎
