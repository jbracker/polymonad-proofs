
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

module Theory.Examples.Haskell.FunctorSet.ListSet {A : Type} (OrdA : OrdInstance {lzero} {lzero} A) where

private
  open module LP = ListProperties OrdA
  open OrdInstance OrdA

Less : (a : A) → (xs : List A) → Set lzero
Less a [] = ⊤
Less a (b ∷ xs) = All (λ x → a ≤ x) (b ∷ xs) × Less b xs

NotEqual : (a : A) → (xs : List A) → Set lzero
NotEqual a [] = ⊤
NotEqual a (b ∷ xs) = All (λ x → ¬ (a == x)) (b ∷ xs) × NotEqual b xs

data LSet : List A → Type where
  nil : LSet []
  cons : (a : A) → {as : List A} 
       → Less a as → NotEqual a as
       → LSet as → LSet (a ∷ as)

less-eq-replace' : {a b : A} {xs : List A} → a == b → All (λ x → a ≤ x) xs → All (λ x → b ≤ x) xs
less-eq-replace' a==b [] = []
less-eq-replace' a==b (a≤x ∷ a≤xs)
  = eq-ord-comp (sym-eq a==b) a≤x ∷ less-eq-replace' a==b a≤xs

less-eq-replace : {a b : A} {xs : List A} → a == b → Less a xs → Less b xs 
less-eq-replace {xs = []} a==b tt = tt
less-eq-replace {xs = x ∷ xs} a==b (a≤x ∷ a≤xs , x≤xs)
  = (eq-ord-comp (sym-eq a==b) a≤x ∷ less-eq-replace' a==b a≤xs) , x≤xs

not-eq-replace' : {a b : A} {xs : List A} → b == a → All (λ x → ¬ (a == x)) xs → All (λ x → ¬ (b == x)) xs
not-eq-replace' a==b [] = []
not-eq-replace' a==b (¬a==x ∷ notEq)
  = (λ b==x → ¬a==x $ trans-eq (sym-eq a==b) b==x) ∷ not-eq-replace' a==b notEq

not-eq-replace : {a b : A} {xs : List A} → b == a → NotEqual a xs → NotEqual b xs
not-eq-replace {xs = []} a==b tt = tt
not-eq-replace {xs = x ∷ xs} a==b (¬a==x ∷ a≠xs , x≠xs) = ((λ b==x → ¬a==x (trans-eq (sym-eq a==b) b==x)) ∷ not-eq-replace' a==b a≠xs) , x≠xs

less-ord-replace' : {a b : A} {xs : List A} → b ≤ a → All (λ x → a ≤ x) xs → All (λ x → b ≤ x) xs
less-ord-replace' b≤a [] = []
less-ord-replace' b≤a (a≤x ∷ a≤xs)
  = trans-ord b≤a a≤x ∷ less-ord-replace' b≤a a≤xs

less-ord-replace : {a b : A} {xs : List A} → b ≤ a → Less a xs → Less b xs
less-ord-replace {xs = []} b≤a tt = tt
less-ord-replace {xs = x ∷ xs} b≤a (a≤x ∷ a≤xs , x≤xs)
  = trans-ord b≤a a≤x ∷ less-ord-replace' b≤a a≤xs , x≤xs

less-extend : {a b : A} {xs : List A} → b ≤ a → Less a xs → Less b (a ∷ xs) 
less-extend {xs = []} b≤a tt = b≤a ∷ [] , tt
less-extend {xs = x ∷ xs} b≤a (a≤x ∷ a≤xs , x≤xs)
  = b≤a ∷ trans-ord b≤a a≤x ∷ less-ord-replace' b≤a a≤xs , a≤x ∷ a≤xs , x≤xs 

less-simplify : {a : A} {xs : List A} → Less a xs → All (λ x → a ≤ x) xs
less-simplify {xs = []} tt = []
less-simplify {xs = x ∷ xs} (a≤x∷xs , x≤xs) = a≤x∷xs


not-eq-simplify : {a : A} {as : List A} → NotEqual a as → All (λ x → ¬ a == x) as
not-eq-simplify {as = []} tt = []
not-eq-simplify {as = x ∷ xs} {¬a==x ∷ a≠xs , x≠xs} = ¬a==x ∷ a≠xs

insert' : A → List A → List A
insert' a [] = a ∷ []
insert' a (b ∷ as) with dec-eq a b
insert' a (b ∷ as) | yes a==b = a ∷ as
insert' a (b ∷ as) | no ¬a==b with dec-ord a b
insert' a (b ∷ as) | no ¬a==b | yes a≤b = a ∷ insert' b as
insert' a (b ∷ as) | no ¬a==b | no ¬a≤b = b ∷ insert' a as

less-insert' : {a b : A} {bs : List A} → a ≤ b → Less b bs → All (λ x → a ≤ x) (insert' b bs)
less-insert' {a} {b} {[]} a≤b tt = a≤b ∷ []
less-insert' {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) with dec-eq b x
less-insert' {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | yes b==x = a≤b ∷ less-ord-replace' a≤b b≤xs
less-insert' {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x with dec-ord b x
less-insert' {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x | yes _ = a≤b ∷ less-insert' (trans-ord a≤b b≤x) x≤xs
less-insert' {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x | no ¬b≤x = ⊥-elim (¬b≤x b≤x)

less-insert : {a b : A} {bs : List A} → a ≤ b → Less b bs → Less a (insert' b bs)
less-insert {bs = []} a≤b tt = a≤b ∷ [] , tt
less-insert {a} {b} {x ∷ xs} a≤b b≤x∷xs with dec-eq b x
less-insert {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | yes b==x
  = a≤b ∷ less-ord-replace' a≤b b≤xs , less-ord-replace b≤x x≤xs
less-insert {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x with dec-ord b x
less-insert {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x | yes _
  = a≤b ∷ less-insert' (trans-ord a≤b b≤x) x≤xs , less-insert b≤x x≤xs
less-insert {a} {b} {x ∷ xs} a≤b (b≤x ∷ b≤xs , x≤xs) | no ¬b==x | no ¬b≤x = ⊥-elim (¬b≤x b≤x)

less-insert-sym' : {a b : A} {bs : List A} → b ≤ a → Less b bs → All (λ x → b ≤ x) (insert' a bs)
less-insert-sym' {bs = []} b≤a b≤xs = b≤a ∷ []
less-insert-sym' {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) with dec-eq a x
less-insert-sym' {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | yes a==x = b≤a ∷ b≤xs
less-insert-sym' {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x with dec-ord a x
less-insert-sym' {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x | yes a≤x
  = b≤a ∷ less-insert-sym' b≤x (less-ord-replace b≤x x≤xs)
less-insert-sym' {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x | no ¬a≤x
  = b≤x ∷ less-insert-sym' b≤a (less-ord-replace b≤x x≤xs)

less-insert-sym : {a b : A} {bs : List A} → b ≤ a → Less b bs → Less b (insert' a bs)
less-insert-sym {bs = []} b≤a tt = b≤a ∷ [] , tt
less-insert-sym {a} {b} {x ∷ xs} b≤a b≤xs with dec-eq a x
less-insert-sym {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | yes a==x
  = b≤a ∷ b≤xs , less-eq-replace (sym-eq a==x) x≤xs
less-insert-sym {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x with dec-ord a x
less-insert-sym {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x | yes a≤x
  = b≤a ∷ less-insert-sym' b≤x (less-ord-replace b≤x x≤xs) , less-insert-sym a≤x (less-ord-replace a≤x x≤xs)
less-insert-sym {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x | no ¬a≤x with excluded-middle-ord ¬a≤x
less-insert-sym {a} {b} {x ∷ xs} b≤a (b≤x ∷ b≤xs , x≤xs) | no ¬a==x | no ¬a≤x | x≤a
  = b≤x ∷ less-insert-sym' b≤a (less-ord-replace b≤x x≤xs) , less-insert-sym x≤a x≤xs


not-eq-insert' : {a b : A} {bs : List A} → ¬(a == b) → NotEqual b bs → All (λ x → ¬ a == x) (insert' b bs)
not-eq-insert' = {!!}


not-eq-insert : {a b : A} {bs : List A} → ¬(a == b) → NotEqual b bs → NotEqual a (insert' b bs)
not-eq-insert {bs = []} ¬a==b tt = ¬a==b ∷ [] , tt
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) with dec-eq b x
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | yes b==x = ⊥-elim (¬b==x b==x)
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | no _ with dec-ord b x
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | no _ | yes b≤x with dec-eq a x
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | no _ | yes b≤x | yes a==x = ⊥-elim (¬a==b {!!})
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | no _ | yes b≤x | no ¬a==x = ¬a==b ∷ not-eq-insert' ¬a==x x≠xs , not-eq-insert ¬b==x x≠xs 
not-eq-insert {a} {b} {x ∷ xs} ¬a==b (¬b==x ∷ b≠xs , x≠xs) | no _ | no ¬b≤x = ({!!} ∷ {!!}) , {!!}

{-
not-eq-insert : {a b : A} {bs : List A} → a ≤ b → ¬(a == b) → NotEqual b bs → Less b bs → NotEqual a (insert' b bs)
not-eq-insert {bs = []} a≤b ¬a==b tt tt = ¬a==b ∷ [] , tt
not-eq-insert {a} {b} {x ∷ xs} a≤b ¬a==b (¬b==x ∷ b≠xs , x≠xs) (b≤x ∷ b≤xs , x≤xs) with dec-eq b x
not-eq-insert {a} {b} {x ∷ xs} a≤b ¬a==b (¬b==x ∷ b≠xs , x≠xs) (b≤x ∷ b≤xs , x≤xs) | yes b==x = ⊥-elim (¬b==x b==x)
not-eq-insert {a} {b} {x ∷ xs} a≤b ¬a==b (¬b==x ∷ b≠xs , x≠xs) (b≤x ∷ b≤xs , x≤xs) | no _ with dec-ord b x
not-eq-insert {a} {b} {x ∷ xs} a≤b ¬a==b (¬b==x ∷ b≠xs , x≠xs) (b≤x ∷ b≤xs , x≤xs) | no _ | yes _
  = (¬a==b ∷ not-eq-insert' (trans-ord a≤b b≤x) (λ a==x → {!!}) x≠xs x≤xs) , not-eq-insert b≤x ¬b==x x≠xs x≤xs
not-eq-insert {a} {b} {x ∷ xs} a≤b ¬a==b (¬b==x ∷ b≠xs , x≠xs) (b≤x ∷ b≤xs , x≤xs) | no _ | no ¬b≤x = ⊥-elim (¬b≤x b≤x)
-}
insert : {as : List A} → (a : A) → LSet as → LSet (insert' a as)
insert a nil = cons a tt tt nil
insert a (cons b {bs} b≤bs b≠bs bs') with dec-eq a b
insert a (cons b {bs} b≤bs b≠bs bs') | yes a==b
  = cons a (less-eq-replace (sym-eq a==b) b≤bs) (not-eq-replace a==b b≠bs) bs'
insert a (cons b {bs} b≤bs b≠bs bs') | no ¬a==b with dec-ord a b
insert a (cons b {bs} b≤bs b≠bs bs') | no ¬a==b | yes a≤b
  = cons a (less-insert a≤b b≤bs) {!!} (insert b bs')
insert a (cons b {bs} b≤bs b≠bs bs') | no ¬a==b | no ¬a≤b with excluded-middle-ord ¬a≤b
insert a (cons b {bs} b≤bs b≠bs bs') | no ¬a==b | no ¬a≤b | b≤a
  = cons b (less-insert-sym b≤a b≤bs) {!!} (insert a bs')







{-

greater-replace : {a b : A} {xs : List A} → a == b → Greater a xs → Greater b xs
greater-replace a==b [] = []
greater-replace a==b (x≤a ∷ greater) = ord-eq-comp x≤a a==b ∷ greater-replace a==b greater


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
