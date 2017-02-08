
-- TODO: Finish proofs
module Theory.Examples.Haskell.FunctorSet where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.List.Any hiding ( map )
open import Data.List.Properties using ( map-id ; map-compose )
open import Data.Nat renaming ( _>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_ ; _≥_ to _≥ℕ_ ) hiding ( _⊔_ ; _≟_ )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
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

open import Theory.Examples.Haskell.FunctorSet.Base
open import Theory.Examples.Haskell.FunctorSet.Sort
open import Theory.Examples.Haskell.FunctorSet.Nub
open import Theory.Examples.Haskell.FunctorSet.NubAndSort

--insert∘map≡map∘insert

map-insert-remove-ignore : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} 
                         → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B)
                         → (g : A → B) → (x : A) → (xs : List A)
                         → ({z y : A} → OrdInstance._==_ OrdA z y → OrdInstance._==_ OrdB (g z) (g y))
                         → map g (insert OrdA x (remove OrdA x xs)) ≡ insert OrdB (g x) (remove OrdB (g x) (map g xs))
map-insert-remove-ignore OrdA OrdB g x [] eqConsistent = refl
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent with OrdInstance.dec-eq OrdA x y
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | yes x==y with OrdInstance.dec-eq OrdB (g x) (g y)
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | yes x==y | yes gx==gy = map-insert-remove-ignore OrdA OrdB g x xs eqConsistent
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | yes x==y | no ¬gx==gy = ⊥-elim (¬gx==gy (eqConsistent x==y))
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | no ¬x==y with OrdInstance.dec-eq OrdB (g x) (g y)
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | no ¬x==y | yes gx==gy with OrdInstance.dec-ord OrdA x y
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | no ¬x==y | yes gx==gy | yes x≤y = {!!}
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | no ¬x==y | yes gx==gy | no ¬x≤y = {!!}
map-insert-remove-ignore OrdA OrdB g x (y ∷ xs) eqConsistent | no ¬x==y | no ¬gx==gy = {!!}

map-nub-sort-ignore : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} 
                    → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B)
                    → (g : A → B) → (xs : List A) 
                    → nub OrdB (sort OrdB (map g (nub OrdA (sort OrdA xs)))) ≡ nub OrdB (sort OrdB (map g xs))
map-nub-sort-ignore OrdA OrdB g [] = refl
map-nub-sort-ignore OrdA OrdB g (x ∷ xs) = begin
  nub OrdB (sort OrdB (map g (nub OrdA (insert OrdA x (sort OrdA xs)))))
    ≡⟨ cong (nub OrdB ∘F sort OrdB ∘F map g) (nub∘insert≡insert∘remove∘nub OrdA x (sort OrdA xs) {!!}) ⟩
  nub OrdB (sort OrdB (map g (insert OrdA x (remove OrdA x (nub OrdA (sort OrdA xs))))))
    ≡⟨ {!!} ⟩
  nub OrdB (insert OrdB (g x) (sort OrdB (map g xs))) ∎

module Test {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B) where
  
  private
    _=A=_ = OrdInstance._==_ OrdA
    _=B=_ = OrdInstance._==_ OrdB
  
  map-sort-insert-shift : (g : A → B) → (x : A) → (xs : List A) 
                        → sort OrdB (map g (insert OrdA x xs)) =A= insert OrdB (g x) (sort OrdB (map g xs))
  map-sort-insert-shift g x [] = refl
  map-sort-insert-shift g x (y ∷ xs) with OrdInstance.dec-ord OrdA x y
  map-sort-insert-shift g x (y ∷ xs) | yes x≤y = refl
  map-sort-insert-shift g x (y ∷ []) | no ¬x≤y with OrdInstance.dec-ord OrdB (g y) (g x) | OrdInstance.dec-ord OrdB (g x) (g y)
  map-sort-insert-shift g x (y ∷ []) | no ¬x≤y | yes gy≤gx | yes gx≤gy = {!!}
  map-sort-insert-shift g x (y ∷ []) | no ¬x≤y | yes gy≤gx | no ¬gx≤gy = refl
  map-sort-insert-shift g x (y ∷ []) | no ¬x≤y | no ¬gy≤gx | yes gx≤gy = refl
  map-sort-insert-shift g x (y ∷ []) | no ¬x≤y | no ¬gy≤gx | no ¬gx≤gy = ⊥-elim (OrdInstance.total-contr OrdB ¬gx≤gy ¬gy≤gx)
  map-sort-insert-shift g x (y ∷ x₁ ∷ xs) | no ¬x≤y = {!!}

map-sort-ignore : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type} 
                → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B)
                → (g : A → B) → (xs : List A) 
                → sort OrdB (map g (sort OrdA xs)) ≡ sort OrdB (map g xs)
map-sort-ignore OrdA OrdB g [] = refl
map-sort-ignore OrdA OrdB g (x ∷ xs) = begin
  sort OrdB (map g (insert OrdA x (sort OrdA xs))) 
    ≡⟨ {!!} ⟩
  insert OrdB (g x) (sort OrdB (map g xs)) ∎

mkListSet : {α : Σ Type (OrdInstance {lzero})} → List (proj₁ α) → ListSet α
mkListSet {α , OrdA} xs = listSet (nub OrdA (sort OrdA xs))
                                  (nub-preserves-sorted OrdA (sort OrdA xs) (sort-produces-sorted OrdA xs))
                                  (nub-produces-no-dup OrdA (sort OrdA xs))

setmap : {α β : Σ Type OrdInstance} → (Σ (proj₁ α → proj₁ β) (λ _ → ⊤)) → ListSet α → ListSet β
setmap {α , OrdA} {β , OrdB} (f , tt) (listSet xs sorted noDup) = mkListSet (map f xs)

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
  ; ctMap = setmap
  ; ctFuncId = ctFuncId
  ; ctFuncComp = ctFuncComp
  ; ctObjProofIrr = {!!}
  ; ctHomProofIrr = {!!}
  } where
    ObjCts : Type → Set (lsuc lzero)
    ObjCts = OrdInstance
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set lzero
    HomCts OrdA OrdB f = ⊤
    
    Obj : Set (lsuc lzero)
    Obj = Σ Type ObjCts

    Hom : Obj → Obj → Set lzero
    Hom α β = Σ (proj₁ α → proj₁ β) (HomCts (proj₂ α) (proj₂ β))
    
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
    
    ctFuncId : {α : Obj} → setmap {α = α} {α} (idF , ctId {proj₁ α} {proj₂ α}) ≡ idF
    ctFuncId {α , OrdA} = funExt helper
      where helper : (x : ListSet (α , OrdA)) → setmap (idF , ctId {α} {OrdA}) x ≡ idF x
            helper (listSet xs sorted noDup) = eqListSet OrdA (nub OrdA (sort OrdA (map idF xs))) xs
              (nub-preserves-sorted OrdA (sort OrdA (map idF xs)) (sort-produces-sorted OrdA (map idF xs))) sorted
              (nub-produces-no-dup OrdA (sort OrdA (map idF xs))) noDup
              (trans (trans (cong (nub OrdA ∘F sort OrdA) (map-id xs))
                            (cong (nub OrdA) (sort-sorting-sorted OrdA xs sorted)))
                     (nub-nubbing-no-dup OrdA xs noDup))

    ctFuncComp : {α β γ : Obj} {f : Hom α β} {g : Hom β γ}
               → setmap {α = α} {γ} (proj₁ g ∘F proj₁ f , _∘Ct_ {proj₁ α} {proj₁ β} {proj₁ γ} {proj₁ g} {proj₁ f} {proj₂ α} {proj₂ β} {proj₂ γ} (proj₂ g) (proj₂ f))
               ≡ setmap {α = β} {γ} g ∘F setmap f
    ctFuncComp {α , OrdA} {β , OrdB} {γ , OrdC} {f , tt} {g , tt} = funExt helper
      where
        helper : (x : ListSet (α , OrdA)) → setmap (g ∘F f , tt) x ≡ (setmap (g , tt) ∘F setmap (f , tt)) x
        helper (listSet xs sorted noDup) = begin
          setmap {α , OrdA} {γ , OrdC} (g ∘F f , tt) (listSet xs sorted noDup)
            ≡⟨ refl ⟩
          listSet (nub OrdC (sort OrdC (map (g ∘F f) xs)))
                  (nub-preserves-sorted OrdC (sort OrdC (map (g ∘F f) xs)) (sort-produces-sorted OrdC (map (g ∘F f) xs)))
                  (nub-produces-no-dup OrdC (sort OrdC (map (g ∘F f) xs)))
            ≡⟨ eqListSet OrdC (nub OrdC (sort OrdC (map (g ∘F f) xs))) (nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                         (nub-preserves-sorted OrdC (sort OrdC (map (g ∘F f) xs)) (sort-produces-sorted OrdC (map (g ∘F f) xs)))
                         (nub-preserves-sorted OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (sort-produces-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                         (nub-produces-no-dup OrdC (sort OrdC (map (g ∘F f) xs)))
                         (nub-produces-no-dup OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs)))) ))
                         helper' ⟩
          listSet (nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                  (nub-preserves-sorted OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) (sort-produces-sorted OrdC (map g (nub OrdB (sort OrdB (map f xs))))))
                  (nub-produces-no-dup OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs)))) ))
            ≡⟨ refl ⟩
          setmap {β , OrdB} {γ , OrdC} (g , tt) (setmap {α , OrdA} {β , OrdB} (f , tt) (listSet xs sorted noDup))
            ≡⟨ refl ⟩
          (setmap {β , OrdB} {γ , OrdC} (g , tt) ∘F setmap {α , OrdA} {β , OrdB} (f , tt)) (listSet xs sorted noDup) ∎
            where
              helper' : nub OrdC (sort OrdC (map (g ∘F f) xs)) ≡ nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs)))))
              helper' = begin
                nub OrdC (sort OrdC (map (g ∘F f) xs))
                  ≡⟨ cong (nub OrdC ∘F sort OrdC) (map-compose xs) ⟩
                nub OrdC (sort OrdC (map g (map f xs)))
                  ≡⟨ sym (map-nub-sort-ignore OrdB OrdC g (map f xs)) ⟩
                nub OrdC (sort OrdC (map g (nub OrdB (sort OrdB (map f xs))))) ∎

