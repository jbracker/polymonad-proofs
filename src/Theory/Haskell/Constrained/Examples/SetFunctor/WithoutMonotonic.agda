

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List hiding ( map )
open import Data.List.Any hiding ( map )
open import Data.List.All hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl )

open import Extensionality
open import Haskell
open import ProofIrrelevance
open import Theory.Category
open import Theory.Category.Dependent
open import Theory.Examples.Haskell.FunctorSet.Base
open import Theory.Haskell.Constrained
open import Theory.Haskell.ConstrainedFunctor

module Theory.Examples.Haskell.FunctorSet.WithoutMonotonic where 



private
  module Map {A : Type} {X : Type} {OrdA : OrdInstance {lzero} {lzero} A} {OrdX : OrdInstance {lzero} {lzero} X} where
    
    
open Map public
    

open ≡-Reasoning

-- insert-adds-in-front : {x : A} {xs : List A} → IsSortedNoDupList OrdA (x ∷ xs) → insert x xs ≡ x ∷ xs
mapList-id : {X : Type} {OrdX : OrdInstance X} 
           → (xs : List X) → IsSortedNoDupList OrdX xs
           → mapList {OrdA = OrdX} {OrdX = OrdX} (λ x → x) xs ≡ xs
mapList-id [] (lift tt) = refl
mapList-id (x ∷ xs) (allX , sortedX) = begin
  insert x (mapList (λ a → a) xs) 
    ≡⟨ cong (insert x) (mapList-id xs sortedX) ⟩
  insert x xs
    ≡⟨ insert-adds-in-front allX ⟩
  x ∷ xs ∎

FunctorLSet : {ℓEq ℓOrd : Level} → ((A : Type) → ProofIrrelevance (OrdInstance {lzero} {lzero} A)) → ConstrainedFunctor {lzero}
FunctorLSet proof-irr-Ord = record
  { Cts = CtCat
  ; F = LSet
  ; map = map
  ; functor-id = functor-id
  ; functor-compose = λ {a} {b} {c} {f} {g} → functor-compose {a} {b} {c} {f} {g}
  ; unique-instances = {!!}
  } where
    ObjCt = OrdInstance {lzero} {lzero}
    
    HomCt : {A B : Type} → ObjCt A → ObjCt B → (A → B) → Set lzero
    HomCt OrdA OrdB f = ⊤
    
    CtCat = dependentCategory ObjCt HomCt (λ _ _ → tt) tt (λ f' g' h' → refl) (λ f' → refl) (λ f' → refl)
    
    open DependentCategory CtCat using ( dep-category )
    open Category
    
    _∘dep_ = _∘_ dep-category
    
    map : {A B : Σ Type ObjCt} → Σ (proj₁ A → proj₁ B) (HomCt (proj₂ A) (proj₂ B)) → LSet A → LSet B
    map (f , tt) set = mapSet f set
    
    open ≡-Reasoning
    
    functor-id : {A : Obj dep-category} → map {A} {A} (id dep-category {A}) ≡ idF
    functor-id {A} = fun-ext helper
      where
        helper : (x : LSet A) → map (id dep-category {A}) x ≡ idF x
        helper (lset [] sorted) = refl
        helper (lset (x ∷ xs) (allX , sortedX)) = lset-eq _ (x ∷ xs) _ (allX , sortedX) $ begin
          insert {OrdA = proj₂ A} x (LSet.xs (mapSet (λ a → a) (lset xs sortedX)))
            ≡⟨ cong (insert {OrdA = proj₂ A} x) (map-structure (λ a → a) (lset xs sortedX)) ⟩
          insert {OrdA = proj₂ A} x (mapList {OrdA = proj₂ A} {OrdX = proj₂ A} (λ a → a) xs)
            ≡⟨ cong (insert {OrdA = proj₂ A} x) (mapList-id xs sortedX) ⟩
          insert {OrdA = proj₂ A} x xs
            ≡⟨ insert-adds-in-front allX ⟩
          x ∷ xs ∎
    
    functor-compose : {α β γ : Obj dep-category}
                    → {f : Hom dep-category α β} {g : Hom dep-category β γ} 
                    → map (_∘dep_ {α} {β} {γ} g f) ≡ map g ∘F map f
    functor-compose {A , OrdA} {B , OrdB} {C , OrdC} {f , tt} {g , tt} = fun-ext (λ xs → helper xs)
      where
        helper : (set : LSet (A , OrdA)) → map (g ∘F f , tt) set ≡ map (g , tt) (map (f , tt) set)
        helper (lset [] (lift tt)) = refl
        helper (lset (x ∷ xs) (allX , sortedX)) = lset-eq _ _ _ _ $ begin
          insert ((g ∘F f) x) (LSet.xs (mapSet (g ∘F f) (lset xs sortedX)))
            ≡⟨ cong (insert (g (f x))) (map-structure (g ∘F f) (lset xs sortedX)) ⟩
          insert (g (f x)) (mapList (g ∘F f) xs)
            ≡⟨ {!!} ⟩
          mapList g (insert (f x) (mapList f xs))
            ≡⟨ cong (mapList g ∘F insert (f x)) (sym (map-structure f (lset xs sortedX))) ⟩
          mapList g (insert (f x) (LSet.xs (mapSet f (lset xs sortedX))))
            ≡⟨ sym (map-structure g (lset (insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))) (insert-preserves-IsSortedNoDupList (LSet.sorted (mapSet f (lset xs sortedX)))))) ⟩
          LSet.xs (mapSet g (lset (insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))) (insert-preserves-IsSortedNoDupList (LSet.sorted (mapSet f (lset xs sortedX)))))) ∎
 
--  map-structure : (f : X → A) → (set : LSet (X , OrdX)) 
--           → LSet.xs (mapSet f set) ≡ mapList f (LSet.xs set)
