
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

open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Product
open import Theory.Haskell.Constrained.Examples.SetFunctor.Map
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert
open import Theory.Haskell.Constrained.Examples.SetFunctor.Union
open import Theory.Haskell.Constrained.Examples.SetFunctor.Instances
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
  ; kext = λ {a} {b} → kext {a} {b}
  ; right-id = λ {A} {B} {k} → fun-ext (r-id {A} {B} k)
  ; left-id = λ {A} → fun-ext (l-id {A})
  ; coher = λ {A} {B} {C} {k} {l} → fun-ext (coher {A} {B} {C} k l)
  } where
    CtCatLSet : Category {suc ℓ} {ℓ}
    CtCatLSet = DependentCategory.DepCat (ConstraintCategoryLSet {ℓ})
    
    ty : Obj CtCatLSet → Set ℓ
    ty A = [ J ]₀ A

    η : {A : Obj CtCatLSet} 
      → [ J ]₀ A → LSet₀ A
    η {A} a = lset (a ∷ []) ([] , (lift tt))
    
    kext : {A B : Obj CtCatLSet} → ([ J ]₀ A → LSet₀ B) → LSet₀ A → LSet₀ B
    kext {A} {B} f (lset [] _) = lset [] (lift tt)
    kext {A} {B} f (lset (x ∷ xs) (sortedX , sortedXs)) = union (f x) (kext {A} {B} f (lset xs sortedXs))

    r-id : {A B : Obj CtCatLSet}
         → (k : [ J ]₀ A → LSet₀ B) 
         → (x : [ J ]₀ A)
         → (kext {A} {B} k ∘F η {A}) x ≡ k x
    r-id k x with k x 
    r-id k x | lset [] _ = refl
    r-id k x | lset (kx ∷ kxs) (sortedKX , sortedKXs) = begin
      insertSet kx (union (lset kxs sortedKXs) (lset [] (lift tt)))
        ≡⟨ cong (insertSet kx) (union-with-empty (lset kxs sortedKXs)) ⟩ 
      insertSet kx (lset kxs sortedKXs)
        ≡⟨ insertSet-adds-in-front kx kxs (sortedKX , sortedKXs) ⟩ 
      lset (kx ∷ kxs) (sortedKX , sortedKXs) ∎
    
    l-id : {A : Obj CtCatLSet}
         → (as : LSet₀ A)
         → kext {A} {A} (η {A}) as ≡ as
    l-id {A} (lset [] _) = refl
    l-id {A} (lset (x ∷ xs) (sortedX , sortedXs)) = begin
         insertSet x (kext (η {A}) (lset xs sortedXs))
           ≡⟨ cong (insertSet x) (l-id (lset xs sortedXs)) ⟩
         insertSet x (lset xs sortedXs)
           ≡⟨ insertSet-adds-in-front x xs (sortedX , sortedXs) ⟩
         lset (x ∷ xs) (sortedX , sortedXs) ∎
    
    kext-union-dist : {A B : Obj CtCatLSet}
                    → (f : ty A → LSet₀ B) 
                    → (xs ys : LSet₀ A)
                    → kext {A} {B} f (union xs ys) ≡ union (kext {A} {B} f xs) (kext {A} {B} f ys)
    kext-union-dist f xs ys = {!!}
    
    coher : {A B C : Obj CtCatLSet}
          → (k : [ J ]₀ A → LSet₀ B) 
          → (l : [ J ]₀ B → LSet₀ C)
          → (x : LSet₀ A)
          → (kext {A} {C} (kext {B} {C} l ∘F k)) x ≡ (kext {B} {C} l ∘F kext {A} {B} k) x
    coher k l (lset [] _) = refl
    coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) with k x
    coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) | lset [] _ = coher k l (lset xs sortedXs)
    coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) | lset (kx ∷ kxs) (sortedKX , sortedKXs) with l kx
    coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) | lset (kx ∷ kxs) (sortedKX , sortedKXs) | lset [] _ = begin
      union (kext l (lset kxs sortedKXs)) ((kext (kext l ∘F k)) (lset xs sortedXs))
        ≡⟨ {!!} ⟩
      kext l (insertSet kx (union (lset kxs sortedKXs) (kext k (lset xs sortedXs)))) ∎
    coher {A} {B} {C} k l (lset (x ∷ xs) (sortedX , sortedXs)) | lset (kx ∷ kxs) (sortedKX , sortedKXs) | lset (lkx ∷ lkxs) sorted = begin
      union (insertSet lkx (union (lset lkxs (proj₂ sorted)) (kext l (lset kxs sortedKXs)))) (kext (kext l ∘F k) (lset xs sortedXs))
        ≡⟨ {!!} ⟩
      union (union (lset (lkx ∷ lkxs) sorted) (kext {B} {C} l (lset kxs sortedKXs))) (kext {A} {C} (kext {B} {C} l ∘F k) (lset xs sortedXs))
        ≡⟨ {!!} ⟩
      union (union (lset (lkx ∷ lkxs) sorted) (kext {B} {C} l (lset kxs sortedKXs))) ((kext {B} {C} l ∘F kext {A} {B} k) (lset xs sortedXs))
        ≡⟨ {!!} ⟩
      kext {B} {C} l (union (lset (kx ∷ kxs) (sortedKX , sortedKXs)) (kext {A} {B} k (lset xs sortedXs)))
        ≡⟨ {!!} ⟩
      kext {B} {C} l (union (lset (kx ∷ kxs) (sortedKX , sortedKXs)) (kext {A} {B} k (lset xs sortedXs)))
        ≡⟨ {!!} ⟩
      kext l (insertSet kx (union (lset kxs sortedKXs) (kext k (lset xs sortedXs)))) ∎ 
{- (lset
       (insert kx
        (LSet.xs (union (lset kxs sortedKXs) (kext k (lset xs sortedXs)))))
       (insert-preserves-IsSortedNoDupList
        (LSet.sorted
         (union (lset kxs sortedKXs) (kext k (lset xs sortedXs)))))) -} 

{- without l kx

 begin
      union (union (l kx) (kext l (lset kxs sortedKXs))) (kext (kext l ∘F k) (lset xs sortedXs))
        ≡⟨ cong (union (union (l kx) (kext {B} {C} l (lset kxs sortedKXs)))) (coher k l (lset xs sortedXs)) ⟩
      union (union (l kx) (kext {B} {C} l (lset kxs sortedKXs))) ((kext {B} {C} l ∘F kext {A} {B} k) (lset xs sortedXs))
        ≡⟨ refl ⟩
      union (union (l kx) (kext {B} {C} l (lset kxs sortedKXs))) (kext {B} {C} l (kext {A} {B} k (lset xs sortedXs)))
        ≡⟨ {!!} ⟩
      kext l (insertSet kx (union (lset kxs sortedKXs) (kext {A} {B} k (lset xs sortedXs)))) ∎

-}

{- without k x

begin
      union ((kext {B} {C} l ∘F k) x) (kext {A} {C} (kext {B} {C} l ∘F k) (lset xs sortedXs))
        ≡⟨ cong (union ((kext {B} {C} l ∘F k) x)) (coher k l (lset xs sortedXs)) ⟩
      union ((kext {B} {C} l ∘F k) x) ((kext {B} {C} l ∘F kext {A} {B} k) (lset xs sortedXs))
        ≡⟨ refl ⟩
      union (kext {B} {C} l (k x)) ((kext {B} {C} l ∘F kext {A} {B} k) (lset xs sortedXs))
        ≡⟨ {!!} ⟩
      kext {B} {C} l (union (k x) (kext {A} {B} k (lset xs sortedXs)))
        ≡⟨ refl ⟩
      (kext {B} {C} l ∘F kext {A} {B} k) (lset (x ∷ xs) (sortedX , sortedXs)) ∎
-}
