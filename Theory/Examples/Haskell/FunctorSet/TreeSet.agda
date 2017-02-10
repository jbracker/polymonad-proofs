
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List renaming ( map to mapList )
open import Data.List.Any hiding ( map )
open import Data.List.All hiding ( map )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality

open import Haskell
open import ProofIrrelevance

open import Theory.Examples.Haskell.FunctorSet.Base

module Theory.Examples.Haskell.FunctorSet.TreeSet {A : Type} (OrdA : OrdInstance {lzero} {lzero} A) where

private
  open module LP = ListProperties OrdA
  open OrdInstance OrdA

Less : (a : A) → (xs : List A) → Set lzero
Less a [] = ⊤
Less a (x ∷ xs) = All (λ x → a ≤ x) (x ∷ xs) × Less x xs 

Greater : (a : A) → (xs : List A) → Set lzero
Greater a [] = ⊤
Greater a (x ∷ xs) = All (λ x → a ≤ x) (x ∷ xs) × Greater x xs

NotEqual : (a : A) → (xs : List A) → Set lzero
NotEqual a [] = ⊤
NotEqual a (x ∷ xs) = All (λ x → ¬ (a == x)) xs × NotEqual x xs

data TreeSet : List A → Type where
  leaf : TreeSet []
  node : (a : A) → {xs zs : List A} 
       → Greater a xs → Less a zs
       → NotEqual a xs → NotEqual a zs
       → TreeSet xs → TreeSet zs → TreeSet (xs ++ (a ∷ []) ++ zs)
{-
less-replace : {a b : A} {xs : List A} → a == b → Less a xs → Less b xs 
less-replace a==b [] = []
less-replace a==b (a≤x ∷ less) = eq-ord-comp (sym-eq a==b) a≤x ∷ less-replace a==b less

greater-replace : {a b : A} {xs : List A} → a == b → Greater a xs → Greater b xs
greater-replace a==b [] = []
greater-replace a==b (x≤a ∷ greater) = ord-eq-comp x≤a a==b ∷ greater-replace a==b greater

not-eq-replace : {a b : A} {xs : List A} → a == b → NotEqual a xs → NotEqual b xs
not-eq-replace a==b [] = []
not-eq-replace a==b (¬a==x ∷ notEq) = (λ b==x → ¬a==x $ trans-eq a==b b==x) ∷ not-eq-replace a==b notEq

middle-elem-contr : {a b c : A} → ¬ (a == b) → a ≤ b → b ≤ c → ¬ (a == c)
middle-elem-contr ¬a==b a≤b b≤c a==c = ¬a==b (antisym-ord a≤b (ord-eq-comp b≤c (sym-eq a==c)))

not-eq-add : {a b : A} {xs : List A} → ¬ (a == b) → a ≤ b → Less b xs → NotEqual b xs → NotEqual a (b ∷ xs)
not-eq-add ¬a==b a≤b [] [] = ¬a==b ∷ []
not-eq-add ¬a==b a≤b (b≤x ∷ less) (¬b==x ∷ notEq) = ¬a==b ∷ (not-eq-add (middle-elem-contr ¬a==b a≤b b≤x) (trans-ord a≤b b≤x) {!!} {!!})

insert : {xs : List A} → (a : A) → TreeSet xs → Σ (List A) TreeSet
insert a leaf = (a ∷ []) , (node a [] [] [] [] leaf leaf)
insert a (node x l≤x x≤r x≠l x≠r l r) with dec-eq x a
insert a (node x {ls} {rs} l≤x x≤r x≠l x≠r l r) | yes x==a = ls ++ (a ∷ []) ++ rs , node a (greater-replace x==a l≤x) (less-replace x==a x≤r) (not-eq-replace x==a x≠l) (not-eq-replace x==a x≠r) l r
insert a (node x l≤x x≤r x≠l x≠r l r) | no ¬x==a with dec-ord x a
insert a (node x l≤x x≤r x≠l x≠r l r) | no ¬x==a | yes x≤a = {!!} , node a {!!} (less-replace {!!} x≤r) {!!} {!!} (node x l≤x [] x≠l [] l leaf) r
insert a (node x l≤x x≤r x≠l x≠r l r) | no ¬x==a | no ¬x≤a = {!!}
-}
