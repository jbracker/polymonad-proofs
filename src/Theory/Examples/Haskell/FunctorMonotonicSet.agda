
-- TODO: Finish proofs
module Theory.Examples.Haskell.FunctorMonotonicSet where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List renaming ( map to mapList )
open import Data.List.Any hiding ( map )
open import Data.List.Properties using ( map-id ; map-compose )
open import Data.Nat renaming ( _>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_ ; _≥_ to _≥ℕ_ ) hiding ( _⊔_ ; _≟_ )
open import Data.Product hiding ( map )
open import Data.Sum hiding ( map )
open import Relation.Nullary
open import Relation.Binary using ( IsDecEquivalence ; IsEquivalence ; IsDecTotalOrder ; IsPreorder )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality hiding ( cong ; sym ; trans )
open ≡-Reasoning


open import Extensionality
open import Congruence
open import Substitution
open import Haskell
open import Haskell.Functor renaming ( Functor to HFunctor )
open import Haskell.Applicative
open import Haskell.Monad
open import Haskell.Monad.List
open import ProofIrrelevance
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Category.Subcategory
open import Theory.Category.Subcategory.Examples
open import Theory.Category.Dependent
open import Theory.Functor
open import Theory.Haskell.Constrained hiding ( Hask )
open import Theory.Haskell.ConstrainedFunctor
open import Theory.Examples.HaskellFunctorToFunctor

open import Theory.Examples.Haskell.FunctorSet.Base
open import Theory.Examples.Haskell.FunctorSet.Sort
open import Theory.Examples.Haskell.FunctorSet.Nub
open import Theory.Examples.Haskell.FunctorSet.NubAndSort

remove∘map∘remove≡remove∘map : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type}
                             → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B)
                             → (f : A → B) → Monotonic OrdA OrdB f → (x : A) → (xs : List A)
                             → remove OrdB (f x) (mapList f (remove OrdA x xs)) ≡ remove OrdB (f x) (mapList f xs)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x [] = refl
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) with OrdInstance.dec-eq OrdA x y | OrdInstance.dec-eq OrdB (f x) (f y)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | yes x==y | yes fx==fy = remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x xs
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | yes x==y | no ¬fx==fy = ⊥-elim (¬fx==fy (monotonic-preserves-equality OrdA OrdB f mon-f x y x==y))
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | yes fx==fy with OrdInstance.dec-eq OrdB (f x) (f y)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | yes fx==fy | yes _ = remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x xs
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | yes fx==fy | no ¬fx==fy = ⊥-elim (¬fx==fy fx==fy)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | no ¬fx==fy with OrdInstance.dec-eq OrdB (f x) (f y)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | no ¬fx==fy | yes fx==fy = ⊥-elim (¬fx==fy fx==fy)
remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (y ∷ xs) | no ¬x==y | no ¬fx==fy | no _ = cong (λ X → f y ∷ X) (remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x xs)

nub∘map∘nub≡nub∘map : {ℓEqA ℓOrdA ℓEqB ℓOrdB : Level} {A B : Type}
                    → (OrdA : OrdInstance {ℓEqA} {ℓOrdA} A) → (OrdB : OrdInstance {ℓEqB} {ℓOrdB} B)
                    → (f : A → B) → Monotonic OrdA OrdB f → (xs : List A)
                    → nub OrdB (mapList f (nub OrdA xs)) ≡ nub OrdB (mapList f xs)
nub∘map∘nub≡nub∘map OrdA OrdB f mon-f [] = refl
nub∘map∘nub≡nub∘map OrdA OrdB f mon-f (x ∷ xs) = cong (λ X → f x ∷ X) $ begin
  remove OrdB (f x) (nub OrdB (mapList f (remove OrdA x (nub OrdA xs))))
    ≡⟨ sym (nub-remove-interchange OrdB (f x) (mapList f (remove OrdA x (nub OrdA xs)))) ⟩
  nub OrdB (remove OrdB (f x) (mapList f (remove OrdA x (nub OrdA xs))))
    ≡⟨ cong (nub OrdB) (remove∘map∘remove≡remove∘map OrdA OrdB f mon-f x (nub OrdA xs)) ⟩
  nub OrdB (remove OrdB (f x) (mapList f (nub OrdA xs)))
    ≡⟨ nub-remove-interchange OrdB (f x) (mapList f (nub OrdA xs)) ⟩
  remove OrdB (f x) (nub OrdB (mapList f (nub OrdA xs)))
    ≡⟨ cong (remove OrdB (f x)) (nub∘map∘nub≡nub∘map OrdA OrdB f mon-f xs) ⟩
  remove OrdB (f x) (nub OrdB (mapList f xs)) ∎

mkListSet : {α : Σ Type OrdInstance} → List (proj₁ α) → ListSet α
mkListSet {α , OrdA} xs = listSet (nub OrdA (sort OrdA xs))
                                  (nub-preserves-sorted OrdA (sort OrdA xs) (sort-produces-sorted OrdA xs))
                                  (nub-produces-no-dup OrdA (sort OrdA xs))

-- Definition of map for Sets represented as ordered lists without duplicates.
map : {α β : Σ Type OrdInstance} → (Σ (proj₁ α → proj₁ β) (Monotonic (proj₂ α) (proj₂ β))) → ListSet α → ListSet β
map {α , OrdA} {β , OrdB} (f , mon-f) (listSet xs sorted noDup) = 
  listSet (nub OrdB (mapList f xs)) 
          (nub-preserves-sorted OrdB (mapList f xs) (monotonic-preserves-sorted OrdA OrdB f mon-f xs sorted))
          (nub-produces-no-dup OrdB (mapList f xs))

-- The constrained functor for Sets in Haskell.
-- The requirement of proof irrelevance for OrdInstance is in one-to-one correspondance with the
-- type class system that Haskell uses in that it there can be only one class instance per type.
FunctorListSet : ({ℓEq ℓOrd : Level} → (A : Type) → ProofIrrelevance (OrdInstance {ℓEq} {ℓOrd} A)) → ConstrainedFunctor {lzero}
FunctorListSet unique-ord-instances = record
  { Cts = Cts
  ; F = F
  ; map = map
  ; functor-id = functor-id
  ; functor-compose = λ {α} {β} {γ} {f} {g} → functor-compose {α} {β} {γ} {f} {g}
  ; unique-instances = (λ α → unique-ord-instances {lzero} {lzero} α) 
                     , unique-hom-inst
  } where
    ObjCts : Type → Set (lsuc lzero)
    ObjCts = OrdInstance
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set lzero
    HomCts OrdA OrdB f = Monotonic OrdA OrdB f
    
    _∘Ct_ : {α β γ : Type} {f : β → γ} {g : α → β} 
        → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ}
        → HomCts β' γ' f → HomCts α' β' g → HomCts α' γ' (f ∘F g)
    _∘Ct_ {A} {B} {C} {f} {g} {OrdA} {OrdB} {OrdC} mon-f mon-g = monotonic-composition OrdA OrdB OrdC f g mon-f mon-g
    
    ctId : {α : Type} {α' : ObjCts α} → HomCts α' α' idF
    ctId a b a≤a = a≤a
    
    assoc : {α β γ δ : Type} 
          → {f : α → β} {g : β → γ} {h : γ → δ}
          → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
          → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h)
          → _∘Ct_ {α} {γ} {δ} {h} {g ∘F f} {α'} {γ'} {δ'} h' (_∘Ct_ {α} {β} {γ} {g} {f} {α'} {β'} {γ'} g' f') 
          ≡ _∘Ct_ {α} {β} {δ} {h ∘F g} {f} {α'} {β'} {δ'} (_∘Ct_ {β} {γ} {δ} {h} {g} {β'} {γ'} {δ'} h' g') f'
    assoc mon-f mon-g mon-h = refl
    
    right-id : {α β : Type} {f : α → β} {α' : ObjCts α} {β' : ObjCts β} 
             → (f' : HomCts α' β' f) → _∘Ct_ {α} {β} {β} {idF} {f} {α'} {β'} {β'} (ctId {β} {β'}) f' ≡ f'
    right-id mon-f = refl
    
    left-id : {α β : Type} {f : α → β} {α' : ObjCts α} {β' : ObjCts β}
            → (f' : HomCts α' β' f) → _∘Ct_ {α} {α} {β} {f} {idF} {α'} {α'} {β'} f' (ctId {α} {α'}) ≡ f'
    left-id mon-f = refl
    
    Cts : ConstraintCategory {lzero}
    Cts = dependentCategory ObjCts HomCts 
                            (λ {α} {β} {γ} {f} {g} {α'} {β'} {γ'} → _∘Ct_ {α} {β} {γ} {f} {g} {α'} {β'} {γ'}) 
                            (λ {α} {α'} → ctId {α} {α'}) 
                            (λ {α} {β} {γ} {δ} {f} {g} {h} {α'} {β'} {γ'} {δ'} f' g' h' → ≡-to-≅ $ assoc {α} {β} {γ} {δ} {f} {g} {h} {α'} {β'} {γ'} {δ'} f' g' h')
                            (λ {α} {β} {f} {α'} {β'} f' → ≡-to-≅ $ right-id {α} {β} {f} {α'} {β'} f') 
                            (λ {α} {β} {f} {α'} {β'} f' → ≡-to-≅ $ left-id {α} {β} {f} {α'} {β'} f')
    
    open DependentCategory Cts
    open Category dep-category
    
    F : Obj → Type
    F (α , OrdA) = ListSet (α , OrdA)
    
    functor-id : {α : Obj} → map {α = α} {α} (idF , ctId {proj₁ α} {proj₂ α}) ≡ idF
    functor-id {α , OrdA} = fun-ext helper
      where helper : (x : ListSet (α , OrdA)) → map (idF , ctId {α} {OrdA}) x ≡ idF x
            helper (listSet xs sorted noDup) = eqListSet OrdA (nub OrdA (mapList idF xs)) xs
              (nub-preserves-sorted OrdA (mapList idF xs) (monotonic-preserves-sorted OrdA OrdA idF (ctId {α' = OrdA}) xs sorted)) sorted
              (nub-produces-no-dup OrdA (mapList idF xs)) noDup
              (nub-map-id OrdA xs noDup)

    functor-compose : {α β γ : Obj} {f : Hom α β} {g : Hom β γ}
               → map {α = α} {γ} (proj₁ g ∘F proj₁ f , _∘Ct_ {proj₁ α} {proj₁ β} {proj₁ γ} {proj₁ g} {proj₁ f} {proj₂ α} {proj₂ β} {proj₂ γ} (proj₂ g) (proj₂ f))
               ≡ map {α = β} {γ} g ∘F map f
    functor-compose {α , OrdA} {β , OrdB} {γ , OrdC} {f , mon-f} {g , mon-g} = fun-ext helper
      where
        helper : (xs : ListSet (α , OrdA)) → map (g ∘F f , monotonic-composition OrdA OrdB OrdC g f mon-g mon-f) xs ≡ (map (g , mon-g) ∘F map (f , mon-f)) xs
        helper (listSet xs sorted noDup) = eqListSet OrdC 
          (nub OrdC (mapList (g ∘F f) xs)) (nub OrdC (mapList g (nub OrdB (mapList f xs)))) 
          (nub-preserves-sorted OrdC (mapList (g ∘F f) xs) 
            (monotonic-preserves-sorted OrdA OrdC (g ∘F f) (monotonic-composition OrdA OrdB OrdC g f mon-g mon-f) xs sorted))
          (nub-preserves-sorted OrdC (mapList g (nub OrdB (mapList f xs))) 
            (monotonic-preserves-sorted OrdB OrdC g mon-g (nub OrdB (mapList f xs)) 
              (nub-preserves-sorted OrdB (mapList f xs) (monotonic-preserves-sorted OrdA OrdB f mon-f xs sorted))))
          (nub-produces-no-dup OrdC (mapList (g ∘F f) xs))
          (nub-produces-no-dup OrdC (mapList g (nub OrdB (mapList f xs))))
          (sym (trans (nub∘map∘nub≡nub∘map OrdB OrdC g mon-g (mapList f xs)) (cong (nub OrdC) (sym (map-compose xs)))))

    unique-hom-inst : {α β : Category.Obj Hask}
                    → (f g : α → β)
                    → (αCt : DepObj α) → (βCt : DepObj β)
                    → (fCt : DepHom αCt βCt f) → (gCt : DepHom αCt βCt g)
                    → fCt ≅ gCt
    unique-hom-inst f g αCt βCt fCt gCt = {!!}
