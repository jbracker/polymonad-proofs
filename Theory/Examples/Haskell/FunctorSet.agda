
-- TODO: Finish proofs
module Theory.Examples.Haskell.FunctorSet where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.Nat renaming ( _>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_ ; _≥_ to _≥ℕ_ ) hiding ( _⊔_ ; _≟_ )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder )
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


open import Utilities renaming ( _∈_ to _∈'_ )
open import Congruence
open import Substitution
open import Haskell
open import Haskell.Functor renaming ( Functor to HFunctor )
open import Haskell.Applicative
open import Haskell.Monad
open import Haskell.Monad.List
open import ProofIrrelevance
open import Theory.Category
open import Theory.Subcategory
open import Theory.Functor
open import Theory.ConstrainedFunctor
open import Theory.Examples.Subcategory
open import Theory.Examples.Category
open import Theory.Examples.HaskellFunctorToFunctor

-------------------------------------------------------------------------------
-- Definition of Eq and Ord instances
-------------------------------------------------------------------------------

-- An 'Eq' instance in Haskell describes a decidable equivalence 
-- relation for its type.
record EqInstance {ℓ : Level} (A : Type) : Set (lsuc ℓ) where
  field
    _==_ : A → A → Set ℓ
    isDecEquivalence : IsDecEquivalence {A = A} _==_

  decEq = IsDecEquivalence._≟_ isDecEquivalence
    
  open Relation.Binary.IsDecEquivalence isDecEquivalence public

-- An 'Ord' instance in Haskell describes a decidable total ordering
-- relation for its type.
record OrdInstance {ℓEq ℓOrd : Level} (A : Type) : Set (lsuc ℓEq ⊔ lsuc ℓOrd) where
  field
    _≤_ : A → A → Set ℓOrd
    eqInstance : EqInstance {ℓ = ℓEq} A
  
  open EqInstance eqInstance public using (_==_ ; decEq)
  
  field
    isDecTotalOrder : IsDecTotalOrder {A = A} _==_ _≤_
  
  dec-ord = IsDecTotalOrder._≤?_ isDecTotalOrder
  
  open Relation.Binary.IsDecTotalOrder isDecTotalOrder public
  
  excluded-middle-ord : {x y : A} → ¬ (x ≤ y) → (y ≤ x)
  excluded-middle-ord {x} {y} ¬x≤y with total x y
  excluded-middle-ord {x} {y} ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  excluded-middle-ord {x} {y} ¬x≤y | inj₂ y≤x = y≤x

-------------------------------------------------------------------------------
-- Definition of predicates on lists
-------------------------------------------------------------------------------

IsSortedList : {ℓEq : Level} {A : Type} → OrdInstance {ℓEq} A → List A → Set lzero
IsSortedList OrdA [] = ⊤
IsSortedList OrdA (x ∷ []) = ⊤
IsSortedList OrdA (x ∷ y ∷ xs) = (x ≤ y) × IsSortedList OrdA (y ∷ xs)
  where _≤_ = OrdInstance._≤_ OrdA

∀List : {ℓ : Level} {A : Type} → (A → Set ℓ) → List A → Set ℓ
∀List p [] = Lift ⊤
∀List p (x ∷ xs) = p x × ∀List p xs

IsNoDupList : {ℓEq ℓOrd : Level} {A : Type} → OrdInstance {ℓEq} {ℓOrd} A → List A → Set (ℓEq ⊔ ℓOrd)
IsNoDupList OrdA [] = Lift ⊤
IsNoDupList OrdA (x ∷ xs) = ∀List (λ y → ¬ (x == y)) xs × IsNoDupList OrdA xs
  where _==_ = OrdInstance._==_ OrdA

law-IsSortedList-forget-elem : {ℓEq : Level} {A : Type} 
                             → (OrdA : OrdInstance {ℓEq} A) → (x : A) → (xs : List A) 
                             → IsSortedList OrdA (x ∷ xs) → IsSortedList OrdA xs
law-IsSortedList-forget-elem OrdA x [] tt = tt
law-IsSortedList-forget-elem OrdA x (y ∷ xs) (x≤y , sorted) = sorted

-------------------------------------------------------------------------------
-- Definition of ordered sets in form of lists
-------------------------------------------------------------------------------

data ListSet (A : Σ Type OrdInstance) : Type where
  listSet : (xs : List (proj₁ A)) → IsSortedList (proj₂ A) xs → IsNoDupList (proj₂ A) xs  → ListSet A

insert : {A : Type} → (OrdA : OrdInstance {lzero} A) → A → Σ (List A) (IsSortedList OrdA) → Σ (List A) (IsSortedList OrdA)
insert OrdA x ([] , tt) = (x ∷ []) , tt
insert OrdA x (y ∷ ys , sorted) with OrdInstance.dec-ord OrdA x y
insert OrdA x (y ∷ ys , sorted) | yes x≤y = (x ∷ y ∷ ys) , (x≤y , sorted)
insert OrdA x (y ∷ ys , sorted) | no ¬x≤y = (y ∷ {!!}) , {!!} -- proj₂ insertRes 
  where insertRes = insert OrdA x (ys , law-IsSortedList-forget-elem OrdA y ys sorted)

sort : {A : Type} → (OrdA : OrdInstance A) → List A → Σ (List A) (IsSortedList OrdA)
sort OrdA [] = [] , tt
sort OrdA (x ∷ xs) = insert OrdA x (sort OrdA xs)

nub : {A : Type} → (OrdA : OrdInstance {lzero} A) → Σ (List A) (IsSortedList OrdA) → Σ (List A) (λ xs → IsSortedList OrdA xs × IsNoDupList OrdA xs)
nub OrdA ([] , sorted) = [] , tt , lift tt
nub OrdA (x ∷ xs , sorted) = {!!}

mkListSet : {α : Σ Type OrdInstance} → List (proj₁ α) → ListSet α
mkListSet {α , OrdA} xs = listSet (proj₁ sortRes) (proj₂ sortRes) {!!}
  where sortRes = sort OrdA xs

setmap : {α β : Σ Type OrdInstance} → (proj₁ α → proj₁ β) → ListSet α → ListSet β
setmap {α , OrdA} {β , OrdB} f (listSet xs sorted noDup) = mkListSet (map f xs)

FunctorListSet : ConstrainedFunctor
FunctorListSet = record
  { ObjCts = ObjCts
  ; HomCts = HomCts
  ; _∘Ct_ = λ {α} {β} {γ} {f} {g} {α'} {β'} {γ'} → _∘Ct_ {α} {β} {γ} {f} {g} {α'} {β'} {γ'}
  ; ctId = λ {α} {α'} → ctId {α} {α'}
  ; ctAssoc = λ {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h} → ctAssoc {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h}
  ; ctIdR = λ {α} {β} {α'} {β'} {f} → ctIdR {α} {β} {α'} {β'} {f}
  ; ctIdL = λ {α} {β} {α'} {β'} {f} → ctIdL {α} {β} {α'} {β'} {f}
  ; F = F
  ; ctMap = {!!}
  ; ctFuncId = {!!}
  ; ctFuncComp = {!!}
  ; ctObjProofIrr = {!!}
  ; ctHomProofIrr = {!!}
  } where
    ObjCts : Type → Set (lsuc lzero)
    ObjCts = OrdInstance
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set lzero
    HomCts OrdA OrdB f = ⊤
    
    Obj : Set (lsuc lzero)
    Obj = Σ Type ObjCts
    
    F : Obj → Type
    F (α , OrdA) = ListSet (α , OrdA)
    
    _∘Ct_ : {α β γ : Type} {f : β → γ} {g : α → β} 
        → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ}
        → HomCts β' γ' f → HomCts α' β' g → HomCts α' γ' (f ∘F g)
    _∘Ct_ tt tt = tt
    
    ctId : {α : Type} {α' : ObjCts α} → HomCts α' α' idF
    ctId = tt
    
    ctAssoc : {α β γ δ : Type} 
            → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
            → {f : α → β} {g : β → γ} {h : γ → δ}
            → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h)
            → _∘Ct_ {α} {γ} {δ} {h} {g ∘F f} {α'} {γ'} {δ'} h' (_∘Ct_ {α} {β} {γ} {g} {f} {α'} {β'} {γ'} g' f') 
            ≡ _∘Ct_ {α} {β} {δ} {h ∘F g} {f} {α'} {β'} {δ'} (_∘Ct_ {β} {γ} {δ} {h} {g} {β'} {γ'} {δ'} h' g') f'
    ctAssoc tt tt tt = refl
    
    ctIdR : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
          → (f' : HomCts α' β' f) → _∘Ct_ {α} {β} {β} {idF} {f} {α'} {β'} {β'} (ctId {β} {β'}) f' ≡ f'
    ctIdR tt = refl
    
    ctIdL : {α β : Type} {α' : ObjCts α} {β' : ObjCts β} {f : α → β}
          → (f' : HomCts α' β' f) → _∘Ct_ {α} {α} {β} {f} {idF} {α'} {α'} {β'} f' (ctId {α} {α'}) ≡ f'
    ctIdL tt = refl
    
{-

law-insert-length : {A : Type} {Eq : EqDict A} 
                  → (ord : OrdDict A Eq) → (x : A) → (xs : List A)
                  → length (insert ord x xs) ≡ suc (length xs) 
law-insert-length ord x [] = prefl
law-insert-length ord x (y ∷ ys) with OrdDict.ordDec ord x y
law-insert-length ord x (y ∷ ys) | yes p = prefl
law-insert-length ord x (y ∷ ys) | no ¬p = cong suc (law-insert-length ord x ys)

law-insert-length-cong : {A : Type} {Eq : EqDict A} 
                       → (ord : OrdDict A Eq) 
                       → (x : A) → (xs ys : List A)
                       → length (x ∷ xs) ≡ length ys → length (insert ord x xs) ≡ length ys
law-insert-length-cong ord x xs ys eq = ptrans (law-insert-length ord x xs) eq

law-sorted-insert' : {A : Type} {EqA : EqDict A}
                   → (ord : OrdDict A EqA)
                   → (x z : A) → (xs : List A)
                   → IsSorted ord (x ∷ xs)
                   → (IsSorted ord (x ∷ insert ord z xs)) 
                   ⊎ (IsSorted ord (z ∷ x ∷ xs))
law-sorted-insert' ord x z [] tt with OrdDict.ordDec ord x z 
law-sorted-insert' ord x z [] tt | yes x≤z = inj₁ $ x≤z , tt
law-sorted-insert' ord x z [] tt | no ¬x≤z with OrdDict.ordTotal ord x z
law-sorted-insert' ord x z [] tt | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-sorted-insert' ord x z [] tt | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , tt
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) with OrdDict.ordDec ord x z
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z with OrdDict.ordDec ord z y
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | yes z≤y = inj₁ $ x≤z , z≤y , sorted[y∷xs]
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y with law-sorted-insert' ord y z xs sorted[y∷xs]
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₁ p = inj₁ $ x≤y , p
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | yes x≤z | no ¬z≤y | inj₂ (z≤y , _) = ⊥-elim (¬z≤y z≤y)
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z with OrdDict.ordTotal ord x z
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₁ x≤z = ⊥-elim (¬x≤z x≤z)
law-sorted-insert' ord x z (y ∷ xs) (x≤y , sorted[y∷xs]) | no ¬x≤z | inj₂ z≤x = inj₂ $ z≤x , x≤y , sorted[y∷xs]

law-sorted-insert : {A : Type} {EqA : EqDict A}
                  → (ord : OrdDict A EqA)
                  → (x : A) → (xs : List A)
                  → IsSorted ord xs
                  → IsSorted ord (insert ord x xs)
law-sorted-insert ord x [] tt = tt
law-sorted-insert ord x (y ∷ []) tt with OrdDict.ordDec ord x y 
law-sorted-insert ord x (y ∷ []) tt | yes x≤y = x≤y , tt
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y with OrdDict.ordTotal ord y x
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y | inj₁ y≤x = y≤x , tt
law-sorted-insert ord x (y ∷ []) tt | no ¬x≤y | inj₂ x≤y = ⊥-elim (¬x≤y x≤y)
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) with OrdDict.ordDec ord x y
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | yes x≤y = x≤y , y≤z , sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y with OrdDict.ordTotal ord x y
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x with OrdDict.ordDec ord x z
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | yes x≤z = y≤x , x≤z , sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z with law-sorted-insert' ord z x xs sorted[z∷xs]
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₁ p = y≤z , p
law-sorted-insert ord x (y ∷ z ∷ xs) (y≤z , sorted[z∷xs]) | no ¬x≤y | inj₂ y≤x | no ¬x≤z | inj₂ (x≤z , _) = ⊥-elim (¬x≤z x≤z)

law-sorted-forget : {A : Type} {EqA : EqDict A} 
                  → (OrdA : OrdDict A EqA) 
                  → (x : A) → (xs : List A) 
                  → IsSorted OrdA (x ∷ xs) → IsSorted OrdA xs
law-sorted-forget OrdA x [] tt = tt
law-sorted-forget OrdA x (y ∷ xs) (_ , sorted) = sorted


law-sort-length : {A : Type} {Eq : EqDict A} 
                → (OrdA : OrdDict A Eq) → (xs : List A)
                → length (sort OrdA xs) ≡ length xs
law-sort-length OrdA [] = prefl
law-sort-length OrdA (x ∷ xs) = law-insert-length-cong OrdA x (sort OrdA xs) (x ∷ xs) (cong suc (law-sort-length OrdA xs))


law-sort-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA (sort OrdA xs)
law-sort-sorted OrdA [] = tt
law-sort-sorted OrdA (x ∷ []) = tt
law-sort-sorted OrdA (x ∷ y ∷ xs) = law-sorted-insert OrdA x (insert OrdA y (sort OrdA xs)) (law-sorted-insert OrdA y (sort OrdA xs) (law-sort-sorted OrdA xs))

law-insert-sorted : {A : Type} {EqA : EqDict A} 
                  → (OrdA : OrdDict A EqA) 
                  → (x : A) → (xs : List A)
                  → IsSorted OrdA (x ∷ xs)
                  → insert OrdA x xs ≡ x ∷ xs
law-insert-sorted OrdA x [] sorted = prefl
law-insert-sorted OrdA x (y ∷ xs) sorted with OrdDict.ordDec OrdA x y 
law-insert-sorted OrdA x (y ∷ xs) sorted | yes _ = prefl
law-insert-sorted OrdA x (y ∷ xs) (x≤y , sorted) | no ¬x≤y = ⊥-elim (¬x≤y x≤y)

law-sort-idempotence : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA xs → sort OrdA xs ≡ xs
law-sort-idempotence OrdA [] sorted = prefl
law-sort-idempotence OrdA (x ∷ []) sorted = prefl
law-sort-idempotence OrdA (x ∷ y ∷ xs) (x≤y , sorted) = begin
  insert OrdA x (insert OrdA y (sort OrdA xs)) 
    ≡⟨ cong (λ X → insert OrdA x (insert OrdA y X)) (law-sort-idempotence OrdA xs (law-sorted-forget OrdA y xs sorted)) ⟩ 
  insert OrdA x (insert OrdA y xs) 
    ≡⟨ cong (insert OrdA x) (law-insert-sorted OrdA y xs sorted) ⟩ 
  insert OrdA x (y ∷ xs) 
    ≡⟨ law-insert-sorted OrdA x (y ∷ xs) (x≤y , sorted) ⟩ 
  x ∷ y ∷ xs ∎

proof-irr-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → (sa sb : IsSorted OrdA xs) → sa ≡ sb 
proof-irr-sorted OrdA [] tt tt = prefl
proof-irr-sorted OrdA (x ∷ []) tt tt = prefl
proof-irr-sorted OrdA (x ∷ y ∷ xs) (p₁ , sa) (p₂ , sb) = cong₂ _,_ (proof-irrelevance p₁ p₂) (proof-irr-sorted OrdA (y ∷ xs) sa sb)



HaskEndomorphism : Category
HaskEndomorphism = endomorphismCategory Hask

HaskEndomorphismInclusionFunctor : Functor HaskEndomorphism Hask
HaskEndomorphismInclusionFunctor = record 
  { F₀ = idF
  ; F₁ = F₁
  ; id = prefl
  ; dist = λ {a} {b} {c} {f} {g} → dist {a} {b} {c} {f} {g}
  } where
    F₁ : {a b : Category.Obj HaskEndomorphism} 
       → Category.Hom HaskEndomorphism a b → Category.Hom Hask (idF a) (idF b)
    F₁ (f , prefl)= f
    
    _∘Hask_ = Category._∘_ Hask
    _∘Endo_ = Category._∘_ HaskEndomorphism
    
    dist : {a b c : Category.Obj HaskEndomorphism}
         → {f : Category.Hom HaskEndomorphism a b}
         → {g : Category.Hom HaskEndomorphism b c}
         → F₁ (g ∘Endo f) ≡ (F₁ g) ∘Hask (F₁ f)
    dist {f = f , prefl} {g , prefl} = prefl

ListFunctor = Applicative.functor $ Monad.applicative monadList

listMap = Functor.fmap ListFunctor

eqListSet : {A : Type} {EqA : EqDict A} 
          → (OrdA : OrdDict A EqA)
          → (s₀ s₁ : List A) 
          → (sorted₀ : IsSorted OrdA s₀) → (sorted₁ : IsSorted OrdA s₁)
          → (s₀ ≡ s₁)
          → listSet s₀ sorted₀ ≡ listSet s₁ sorted₁
eqListSet OrdA s₀ .s₀ sorted₀ sorted₁ prefl = cong (listSet s₀) (proof-irr-sorted OrdA s₀ sorted₀ sorted₁)

law-swap-insert-insert : {A : Type} {EqA : EqDict A} 
                       → (OrdA : OrdDict A EqA) 
                       → (x y : A) → (xs : List A) 
                       → insert OrdA x (insert OrdA y xs) ≡ insert OrdA y (insert OrdA x xs)
law-swap-insert-insert OrdA x y [] with OrdDict.ordDec OrdA x y
law-swap-insert-insert OrdA x y [] | yes x≤y with OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y [] | yes x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y [] | yes x≤y | no ¬y≤x = prefl
law-swap-insert-insert OrdA x y [] | no ¬x≤y with OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y [] | no ¬x≤y | yes y≤x = prefl
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x with OrdDict.ordTotal OrdA x y
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-swap-insert-insert OrdA x y [] | no ¬x≤y | no ¬y≤x | inj₂ y≤x = ⊥-elim (¬y≤x y≤x)
law-swap-insert-insert OrdA x y (z ∷ xs) with OrdDict.ordDec OrdA x y | OrdDict.ordDec OrdA y x
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x with OrdDict.ordDec OrdA x z | OrdDict.ordDec OrdA y z 
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | yes x≤z | yes y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | yes x≤z | no ¬y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | no ¬x≤z | yes y≤z = ⊥-elim (¬x≤z (OrdDict.ordTrans OrdA x y z x≤y y≤z))
law-swap-insert-insert OrdA x y (z ∷ xs) | yes x≤y | no ¬y≤x | no ¬x≤z | no ¬y≤z = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | yes y≤x = {!!}
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x with OrdDict.ordTotal OrdA x y
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
law-swap-insert-insert OrdA x y (z ∷ xs) | no ¬x≤y | no ¬y≤x | inj₂ y≤x = ⊥-elim (¬y≤x y≤x)


law-swap-insert-sort : {A : Type} {EqA : EqDict A} 
                     → (OrdA : OrdDict A EqA) 
                     → (x : A) → (xs : List A) 
                     → insert OrdA x (sort OrdA xs) ≡ sort OrdA (insert OrdA x xs)
law-swap-insert-sort OrdA x [] = prefl
law-swap-insert-sort OrdA x (y ∷ xs) with OrdDict.ordDec OrdA x y
law-swap-insert-sort OrdA x (y ∷ xs) | yes x≤y = prefl
law-swap-insert-sort OrdA x (y ∷ xs) | no ¬x≤y = begin
  insert OrdA x (insert OrdA y (sort OrdA xs))  
    ≡⟨ law-swap-insert-insert OrdA x y (sort OrdA xs) ⟩
  insert OrdA y (insert OrdA x (sort OrdA xs)) 
    ≡⟨ cong (insert OrdA y) (law-swap-insert-sort OrdA x xs) ⟩
  insert OrdA y (sort OrdA (insert OrdA x xs)) ∎

ListSetFunctor : Functor HaskOrd Hask
ListSetFunctor = functor F₀ F₁ (λ {a} → id {a}) (λ {a} {b} {c} {f} {g} → dist {a} {b} {c} {f} {g})
  where
    F₀ : Category.Obj HaskOrd → Category.Obj Hask
    F₀ A = ListSet A
    
    F₁ : {a b : Category.Obj HaskOrd} → Category.Hom HaskOrd a b → Category.Hom Hask (F₀ a) (F₀ b)
    F₁ f (listSet xs _) = mkListSet (listMap f xs)
    
    _∘H_ = Category._∘_ Hask

    id : {A : Category.Obj HaskOrd} → F₁ (Category.id HaskOrd {A}) ≡ Category.id Hask {F₀ A}
    id {A , EqA , OrdA} = funExt helperId
      where
        helperId : (s : ListSet (A , EqA , OrdA)) 
                 → F₁ (Category.id HaskOrd {A , EqA , OrdA}) s ≡ Category.id Hask {F₀ (A , EqA , OrdA)} s
        helperId (listSet s sorted) = begin
          F₁ (Category.id HaskOrd {A , EqA , OrdA}) (listSet s sorted) 
            ≡⟨ prefl ⟩
          F₁ idF (listSet s sorted) 
            ≡⟨ prefl ⟩
          mkListSet (listMap idF s)
            ≡⟨ cong mkListSet (cong (λ X → X s) (Functor.lawId ListFunctor)) ⟩
          mkListSet s
            ≡⟨ prefl ⟩
          listSet (sort OrdA s) (law-sort-sorted OrdA s)
            ≡⟨ eqListSet OrdA (sort OrdA s) s (law-sort-sorted OrdA s) sorted (law-sort-idempotence OrdA s sorted) ⟩
          listSet s sorted ∎ 
    
    dist : {A B C : Category.Obj HaskOrd} 
         → {f : Category.Hom HaskOrd A B} → {g : Category.Hom HaskOrd B C}
         → F₁ (g ∘H f) ≡ F₁ g ∘H F₁ f
    dist {A , EqA , OrdA} {B , EqB , OrdB} {C , EqC , OrdC} {f} {g} = funExt helper
      where
        helper' : (s : List A) → sort OrdC (listMap (g ∘H f) s) ≡ sort OrdC (listMap g (sort OrdB (listMap f s)))
        helper' [] = prefl
        helper' (x ∷ xs) = begin
          insert OrdC ((g ∘H f) x) (sort OrdC (listMap (g ∘H f) xs))
            ≡⟨ prefl ⟩
          insert OrdC (g (f x)) (sort OrdC (listMap (g ∘H f) xs))
            ≡⟨ cong (insert OrdC (g (f x))) (helper' xs) ⟩
          insert OrdC (g (f x)) (sort OrdC (listMap g (sort OrdB (listMap f xs))))
            ≡⟨ {!!} ⟩
          sort OrdC (listMap g (insert OrdB (f x) (sort OrdB (listMap f xs)))) ∎
        
        helper : (s : ListSet (A , EqA , OrdA)) → F₁ (g ∘H f) s ≡ (F₁ g ∘H F₁ f) s
        helper (listSet s sorted) = begin
          mkListSet (listMap (g ∘H f) s) 
            ≡⟨ prefl ⟩
          listSet (sort OrdC (listMap (g ∘H f) s)) (law-sort-sorted OrdC (listMap (g ∘H f) s))
            ≡⟨ eqListSet OrdC (sort OrdC (listMap (g ∘H f) s)) (sort OrdC (listMap g (sort OrdB (listMap f s)))) (law-sort-sorted OrdC (listMap (g ∘H f) s)) (law-sort-sorted OrdC (listMap g (sort OrdB (listMap f s)))) (helper' s) ⟩
          listSet (sort OrdC (listMap g (sort OrdB (listMap f s)))) (law-sort-sorted OrdC (listMap g (sort OrdB (listMap f s))))
            ≡⟨ prefl ⟩
          mkListSet (listMap g (sort OrdB (listMap f s)))
            ≡⟨ prefl ⟩
          F₁ g (listSet (sort OrdB (listMap f s)) (law-sort-sorted OrdB (listMap f s)))
            ≡⟨ prefl ⟩
          (F₁ g ∘H F₁ f) (listSet s sorted) ∎

listSetMap : {A B : Category.Obj HaskOrd} → (proj₁ A → proj₁ B) → ListSet A  → ListSet B
listSetMap = Functor.F₁ ListSetFunctor

-- law-sort-idempotence : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → IsSorted OrdA xs → sort OrdA xs ≡ xs
-- proof-irr-sorted : {A : Type} {EqA : EqDict A} → (OrdA : OrdDict A EqA) → (xs : List A) → (sa sb : IsSorted OrdA xs) → sa ≡ sb
 
-}
