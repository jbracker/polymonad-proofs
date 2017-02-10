
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List renaming ( map to mapList )
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
open B.ListProperties
open import Theory.Examples.Haskell.FunctorSet.Sort
open import Theory.Examples.Haskell.FunctorSet.Nub
open import Theory.Examples.Haskell.FunctorSet.NubAndSort

module Theory.Examples.Haskell.FunctorSet.ListMap {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} (OrdA : B.OrdInstance {ℓEqA} {ℓOrdA} A) (OrdB : B.OrdInstance {ℓEqB} {ℓOrdB} B) where
  
private
  open module M = B.Monotonic OrdA OrdB

{-
map-preserves-sorted : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {α β : Type} 
                     → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} α) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} β) 
                     → (f : α → β) → (xs : List α) 
                     → IsSortedList OrdA xs → IsSortedList OrdB (map' OrdA OrdB f xs)
  map'-preserves-sorted OrdA OrdB f [] (lift tt) = lift tt
  map'-preserves-sorted OrdA OrdB f (x ∷ xs) sorted 
    = (insert-preserves-sorted OrdB (f x) (remove OrdB (f x) (map' OrdA OrdB f xs)) 
        (remove-preserves-sorted OrdB (f x) (map' OrdA OrdB f xs) 
          (map'-preserves-sorted OrdA OrdB f xs (IsSortedList-forget-elem OrdA x xs sorted))))
-}


map-preserves-sorted : (f : A → B) → Monotonic f → (xs : List A) 
                     → (IsSortedList OrdA xs) → (IsSortedList OrdB (mapList f xs))
map-preserves-sorted f mon-f [] sorted = lift tt
map-preserves-sorted f mon-f (x ∷ []) sorted = lift tt
map-preserves-sorted f mon-f (x ∷ y ∷ xs) (x≤y , sorted) = mon-f x y x≤y , map-preserves-sorted f mon-f (y ∷ xs) sorted

map-preserves-missing-elem : (f : A → B) → Monotonic f → (x : A) → (xs : List A) 
                           → ¬ (InList OrdA x xs) → ¬ (InList OrdB (f x) (mapList f xs))
map-preserves-missing-elem f mon-f x [] ¬x∈xs = λ ()
map-preserves-missing-elem f mon-f x (x₁ ∷ xs) ¬x∈xs x₂ = {!!}

map-preserves-no-dup : (f : A → B) → Monotonic f → (xs : List A) 
                     → IsNoDupList OrdA xs → IsNoDupList OrdB (mapList f xs)
map-preserves-no-dup f mon-f [] noDup = lift tt
map-preserves-no-dup f mon-f (x ∷ xs) (¬x∈xs , noDup) = map-preserves-missing-elem f mon-f x xs ¬x∈xs , map-preserves-no-dup f mon-f xs noDup
