
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List hiding ( map )
open import Data.List.Any hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Haskell
open import ProofIrrelevance

import Theory.Examples.Haskell.FunctorSet.Base as B

open import Theory.Examples.Haskell.FunctorSet.Base using ( OrdInstance )

module Theory.Examples.Haskell.FunctorSet.NubAndSort {ℓEq ℓOrd : Level} {A : Type} (OrdA : OrdInstance {ℓEq} {ℓOrd} A) where
  
private
  import Theory.Examples.Haskell.FunctorSet.Sort as S
  import Theory.Examples.Haskell.FunctorSet.Nub as N
  
  open module ListPropertiesA = B.ListProperties OrdA
  open module SortA = S OrdA
  open module NubA = N OrdA
  open B.OrdInstance OrdA
  
insert-remove-preserves-no-dup : (x : A) → (xs : List A) 
                               → IsNoDupList xs → IsNoDupList (insert x $ remove x xs)
insert-remove-preserves-no-dup y [] (lift tt) = (λ ()) , lift tt
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) with dec-eq y x
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | yes y==x = insert-remove-preserves-no-dup y xs noDup
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x with dec-ord y x
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x | yes y≤x 
  = ¬InList-prepend-elem y x (remove y xs) ¬y==x (remove-produces-missing-elem y xs) 
  , remove-preserves-missing-elem y x xs ¬x∈xs 
  , remove-preserves-no-dup y xs noDup
insert-remove-preserves-no-dup y (x ∷ xs) (¬x∈xs , noDup) | no ¬y==x | no ¬y≤x 
  = insert-preserves-missing-elem x y (remove y xs) (sym-not-eq ¬y==x) (remove-preserves-missing-elem y x xs ¬x∈xs) 
  , insert-remove-preserves-no-dup y xs noDup
  
insert-remove-elim : (x : A) → (xs ys : List A)
                   → xs ≡ ys
                   → IsSortedList (x ∷ xs) → IsNoDupList (x ∷ xs)
                   → insert x (remove x xs) ≡ x ∷ ys
insert-remove-elim y [] .[] refl (lift tt) (¬y∈[] , lift tt) = refl
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) with dec-eq y x
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | yes y==x = ⊥-elim (¬y∈x∷xs (here y==x))
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x with dec-ord y x
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x | yes _ 
  = cong (λ X → y ∷ x ∷ X) (remove-removing-missing-elem y xs (¬InList-forget-elem y x xs ¬y∈x∷xs))
insert-remove-elim y (x ∷ xs) ._ refl (y≤x , sorted) (¬y∈x∷xs , ¬x∈xs , noDup) | no ¬y==x | no ¬y≤x = ⊥-elim (¬y≤x y≤x)
  
nub∘insert≡insert∘remove∘nub : (x : A) → (xs : List A)
                             → IsSortedList (x ∷ xs)
                             → nub (insert x xs) ≡ insert x (remove x (nub xs))
nub∘insert≡insert∘remove∘nub x [] sorted = refl
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) with dec-ord x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ with dec-eq x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | yes x==y 
  = sym (insert-smallest-in-front x 
        (remove x (remove y (nub xs))) 
          (remove-preserves-sorted' x x (remove y (nub xs)) 
            (remove-preserves-sorted' y x (nub xs) 
              (nub-preserves-sorted' x xs 
                (IsSortedList-replace-elem y x xs x≤y sorted)))))
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y with dec-ord x y
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y | yes _ = refl
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | yes _ | no ¬x==y | no ¬x≤y = ⊥-elim (¬x≤y x≤y)
nub∘insert≡insert∘remove∘nub x (y ∷ xs) (x≤y , sorted) | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

sort∘nub≡nub∘sort : (xs : List A) → IsSortedList xs
                  → sort (nub xs) ≡ nub (sort xs)
sort∘nub≡nub∘sort [] sorted = refl
sort∘nub≡nub∘sort (x ∷ xs) sorted = begin
  insert x (sort (remove x (nub xs)))
    ≡⟨ cong (insert x) (sort-sorting-sorted (remove x (nub xs)) (remove-preserves-sorted x (nub xs) (nub-preserves-sorted xs (IsSortedList-forget-elem x xs sorted)))) ⟩
  insert x (remove x (nub xs))
    ≡⟨ cong (insert x) (sym $ nub-remove-interchange x xs) ⟩
  insert x (nub (remove x xs))
    ≡⟨ cong (insert x) (nub-remove-interchange x xs) ⟩
  insert x (remove x (nub xs))
    ≡⟨ sym (nub∘insert≡insert∘remove∘nub x xs sorted) ⟩
  nub (insert x xs)
    ≡⟨ cong (nub ∘F insert x) (sym (sort-sorting-sorted xs (IsSortedList-forget-elem x xs sorted))) ⟩
  nub (insert x (sort xs)) ∎


{-

private
  Obj : {ℓEq ℓOrd : Level} → Set (lsuc (ℓOrd ⊔ ℓEq)) 
  Obj {ℓEq} {ℓOrd} = Σ Type (OrdInstance {ℓEq} {ℓOrd})
  
private
  Hom : {ℓEq ℓOrd : Level} → Obj {ℓEq} {ℓOrd} → Obj {ℓEq} {ℓOrd} → Set lzero
  Hom (α , OrdA) (β , OrdB) = Σ (α → β) (λ _ → ⊤)


private
  map' : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {α β : Type} 
       → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} α) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} β) 
       → (α → β) → List α → List β
  map' OrdA OrdB _ [] = []
  map' OrdA OrdB f (x ∷ xs) = insert OrdB (f x) $ remove OrdB (f x) $ map' OrdA OrdB f xs

private
  map'-preserves-sorted : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {α β : Type} 
                        → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} α) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} β) 
                        → (f : α → β) → (xs : List α) 
                        → IsSortedList OrdA xs → IsSortedList OrdB (map' OrdA OrdB f xs)
  map'-preserves-sorted OrdA OrdB f [] (lift tt) = lift tt
  map'-preserves-sorted OrdA OrdB f (x ∷ xs) sorted 
    = (insert-preserves-sorted OrdB (f x) (remove OrdB (f x) (map' OrdA OrdB f xs)) 
        (remove-preserves-sorted OrdB (f x) (map' OrdA OrdB f xs) 
          (map'-preserves-sorted OrdA OrdB f xs (IsSortedList-forget-elem OrdA x xs sorted))))

private
  map'-preserves-no-dup : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {α β : Type} 
                        → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} α) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} β) 
                        → (f : α → β) → (xs : List α) 
                        → IsNoDupList OrdA xs → IsNoDupList OrdB (map' OrdA OrdB f xs)
  map'-preserves-no-dup OrdA OrdB f [] (lift tt) = lift tt
  map'-preserves-no-dup OrdA OrdB f (x ∷ xs) (¬x∈xs , noDup) 
    = (insert-remove-preserves-no-dup OrdB (f x) (map' OrdA OrdB f xs) 
        (map'-preserves-no-dup OrdA OrdB f xs noDup))


map : {α β : Obj} → Hom α β → ListSet α → ListSet β
map {α , OrdA} {β , OrdB} (f , tt) (listSet [] sorted noDup) = listSet [] (lift tt) (lift tt)
map {α , OrdA} {β , OrdB} (f , tt) (listSet (x ∷ []) sorted noDup) = listSet (f x ∷ []) (lift tt) ((λ ()) , lift tt)
map {α , OrdA} {β , OrdB} (f , tt) (listSet (x ∷ y ∷ xs) (x<y , sorted) (¬x∈y∷xs , ¬y∈xs , noDup)) = 
  listSet (map' OrdA OrdB f (x ∷ y ∷ xs)) 
          (insert-preserves-sorted OrdB (f x) (remove OrdB (f x) (insert OrdB (f y) (remove OrdB (f y) (map' OrdA OrdB f xs)))) 
            (remove-preserves-sorted OrdB (f x) (insert OrdB (f y) (remove OrdB (f y) (map' OrdA OrdB f xs))) 
              (insert-preserves-sorted OrdB (f y) (remove OrdB (f y) (map' OrdA OrdB f xs)) 
                (remove-preserves-sorted OrdB (f y) (map' OrdA OrdB f xs) 
                  (map'-preserves-sorted OrdA OrdB f xs (IsSortedList-forget-elem OrdA y xs sorted)))))) 
          (insert-remove-preserves-no-dup OrdB (f x) (insert OrdB (f y) (remove OrdB (f y) (map' OrdA OrdB f xs))) 
            (insert-remove-preserves-no-dup OrdB (f y) (map' OrdA OrdB f xs) 
              (map'-preserves-no-dup OrdA OrdB f xs noDup)))

private
  map'-id : {ℓEq ℓOrd : Level} {A : Type} → (OrdA : OrdInstance {ℓEq} {ℓOrd} A) 
          → (xs : List A)
          → IsSortedList OrdA xs → IsNoDupList OrdA xs
          → map' OrdA OrdA idF xs ≡ xs
  map'-id OrdA [] (lift tt) (lift tt) = refl
  map'-id OrdA (x ∷ xs) sorted (¬x∈xs , noDup)
    = insert-remove-elim OrdA x (map' OrdA OrdA idF xs) xs 
                         (map'-id OrdA xs (IsSortedList-forget-elem OrdA x xs sorted) noDup) 
                         (subst (λ X → IsSortedList OrdA (x ∷ X)) (sym (map'-id OrdA xs (IsSortedList-forget-elem OrdA x xs sorted) noDup)) sorted)
                         (subst (λ X → ¬ InList OrdA x X) (sym (map'-id OrdA xs (IsSortedList-forget-elem OrdA x xs sorted) noDup)) ¬x∈xs , map'-preserves-no-dup OrdA OrdA idF xs noDup)


map-id : {α : Obj} → map {α = α} {α} (idF , tt) ≡ idF
map-id {α , OrdA} = funExt map-id'
  where
    map-id' : (x : ListSet (α , OrdA)) → map (idF , tt) x ≡ idF x
    map-id' (listSet [] (lift tt) (lift tt)) = refl
    map-id' (listSet (x ∷ []) (lift tt) (¬x∈[] , lift tt)) = cong (λ X → listSet (x ∷ []) (lift tt) (X , lift tt)) (proof-irr-¬ (λ ()) ¬x∈[])
    map-id' (listSet (x ∷ y ∷ xs) (x≤y ,  sorted) (¬x∈y∷xs , ¬y∈xs , noDup)) 
      = eqListSet OrdA (insert OrdA x (remove OrdA x (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs))))) 
                       (x ∷ y ∷ xs) 
                       (insert-preserves-sorted OrdA x 
                         (remove OrdA x (insert OrdA y (remove OrdA y (map' OrdA OrdA (λ z → z) xs))))
                         (remove-preserves-sorted OrdA x
                           (insert OrdA y (remove OrdA y (map' OrdA OrdA (λ z → z) xs)))
                           (insert-preserves-sorted OrdA y (remove OrdA y (map' OrdA OrdA (λ z → z) xs))
                             (remove-preserves-sorted OrdA y (map' OrdA OrdA (λ z → z) xs)
                               (map'-preserves-sorted OrdA OrdA (λ z → z) xs (IsSortedList-forget-elem OrdA y xs sorted))))))
                       (x≤y , sorted) 
                       (insert-remove-preserves-no-dup OrdA x
                         (insert OrdA y (remove OrdA y (map' OrdA OrdA (λ z → z) xs)))
                         (insert-remove-preserves-no-dup OrdA y
                           (map' OrdA OrdA (λ z → z) xs)
                           (map'-preserves-no-dup OrdA OrdA (λ z → z) xs noDup)))
                       (¬x∈y∷xs , ¬y∈xs , noDup)
                       map-id-helper
      where
        map-expr = map' OrdA OrdA idF xs
        
        map-id-helper : insert OrdA x (remove OrdA x (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs)))) ≡ x ∷ y ∷ xs
        map-id-helper = begin
          insert OrdA x (remove OrdA x (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs)))) 
            ≡⟨ insert-remove-elim OrdA x 
                                  (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs))) 
                                  (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs))) 
                                  refl
                                  (insert-preserves-sorted' OrdA x y (remove OrdA y (map' OrdA OrdA (λ z → z) xs)) x≤y (remove-preserves-sorted' OrdA y x (map' OrdA OrdA (λ z → z) xs) {!!})) 
                                  ({!!} , insert-remove-preserves-no-dup OrdA y (map' OrdA OrdA (λ z → z) xs) (map'-preserves-no-dup OrdA OrdA (λ z → z) xs noDup)) ⟩
          x ∷ (insert OrdA y (remove OrdA y (map' OrdA OrdA idF xs))) 
            ≡⟨ cong (λ X → x ∷ (insert OrdA y (remove OrdA y X))) (map'-id OrdA xs (IsSortedList-forget-elem OrdA y xs sorted) noDup) ⟩
          x ∷ (insert OrdA y (remove OrdA y xs)) 
            ≡⟨ cong (λ X → x ∷ X) (insert-remove-elim OrdA y xs xs refl sorted (¬y∈xs , noDup)) ⟩
          x ∷ y ∷ xs ∎
-}
