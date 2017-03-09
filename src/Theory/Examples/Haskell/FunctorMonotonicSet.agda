
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
open import Equality
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
open import Theory.Examples.Haskell.FunctorSet.Map
open import Theory.Examples.Haskell.FunctorSet.NubAndSort

module Theory.Examples.Haskell.FunctorMonotonicSet where

mkListSet : {α : Σ Type OrdInstance} → List (proj₁ α) → ListSet α
mkListSet {α , OrdA} xs = listSet (nub OrdA (sort OrdA xs))
                                  (nub-preserves-sorted OrdA (sort OrdA xs) (sort-produces-sorted OrdA xs))
                                  (nub-produces-no-dup OrdA (sort OrdA xs))

-- Definition of map for Sets represented as ordered lists without duplicates.
map : {α β : Σ Type OrdInstance} → (proj₁ α → proj₁ β) → ListSet α → ListSet β
map {α , OrdA} {β , OrdB} f (listSet xs sorted noDup) = 
  listSet (nub OrdB (sort OrdB (mapList f xs))) 
          (nub-preserves-sorted OrdB (sort OrdB (mapList f xs)) (sort-produces-sorted OrdB (mapList f xs)))
          (nub-produces-no-dup OrdB (sort OrdB (mapList f xs)))

-- The constrained functor for Sets in Haskell.
-- The requirement of proof irrelevance for OrdInstance is in one-to-one correspondance with the
-- type class system that Haskell uses in that it there can be only one class instance per type.
FunctorListSet : ({ℓEq ℓOrd : Level} → (A : Type) → ProofIrrelevance (OrdInstance {ℓEq} {ℓOrd} A)) → ConstrainedFunctor {lzero}
FunctorListSet unique-ord-instances = record
  { Cts = Cts
  ; F = F
  ; map = λ {α} {β} → fmap {α} {β}
  ; functor-id = λ {α} → functor-id {α}
  ; functor-compose = λ {α} {β} {γ} {f} {g} → functor-compose {α} {β} {γ} {f} {g}
  ; unique-instances = unique-instances
  } where
    
    ObjCts : Type → Set (lsuc lzero)
    ObjCts A = Σ (OrdInstance A) IsStructuralEquality
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set lzero
    HomCts _ _ _ = ⊤
    
    _∘Ct_ : {α β γ : Type} {f : β → γ} {g : α → β} 
        → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ}
        → HomCts β' γ' f → HomCts α' β' g → HomCts α' γ' (f ∘F g)
    _∘Ct_ {A} {B} {C} {f} {g} {OrdA} {OrdB} {OrdC} _ _ = tt
    
    ctId : {α : Type} {α' : ObjCts α} → HomCts α' α' idF
    ctId = tt
    
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
    
    Obj' : Obj → Σ Type OrdInstance
    Obj' (A , OrdA , _) = A , OrdA
    
    F : Obj → Type
    F (α , OrdA , struct-eqA) = ListSet (α , OrdA)
    
    fmap : {α β : Obj} → Hom α β → ListSet (Obj' α) → ListSet (Obj' β)
    fmap (f , tt) a = map f a
    
    functor-id : {α : Obj} → fmap {α} {α} (id {α}) ≡ idF
    functor-id {α , OrdA , struct-eqA} = fun-ext helper
      where
        helper' : (xs : List α) → IsSortedList OrdA xs → IsNoDupList OrdA xs → nub OrdA (sort OrdA (mapList (λ z → z) xs)) ≡ xs
        helper' [] sorted noDup = refl
        helper' (x ∷ xs) sorted noDup = begin
          nub OrdA (insert OrdA x (sort OrdA (mapList (λ z → z) xs)))
            ≡⟨ cong (λ X → nub OrdA (insert OrdA x (sort OrdA X))) (map-id xs) ⟩
          nub OrdA (insert OrdA x (sort OrdA xs))
            ≡⟨ cong (λ X → nub OrdA (insert OrdA x X)) (sort-sorting-sorted OrdA xs (IsSortedList-forget-elem OrdA x xs sorted)) ⟩
          nub OrdA (insert OrdA x xs)
            ≡⟨ nub∘insert≡insert∘remove∘nub OrdA x xs sorted ⟩
          insert OrdA x (remove OrdA x (nub OrdA xs))
            ≡⟨ cong (λ X → insert OrdA x (remove OrdA x X)) (nub-nubbing-no-dup OrdA xs xs refl (proj₂ noDup)) ⟩
          insert OrdA x (remove OrdA x xs)
            ≡⟨ cong (insert OrdA x) (remove-removing-missing-elem OrdA x xs (proj₁ noDup)) ⟩
          insert OrdA x xs
            ≡⟨ insert-smallest-in-front OrdA x xs sorted ⟩
          x ∷ xs ∎
        
        helper : (x : ListSet (α , OrdA)) → fmap {α , OrdA , struct-eqA} {α , OrdA , struct-eqA} (id {α , OrdA , struct-eqA}) x ≡ idF x
        helper (listSet xs sorted noDup) 
          = eqListSet OrdA 
            (nub OrdA (sort OrdA (mapList (λ z → z) xs))) xs 
            (nub-preserves-sorted OrdA (sort OrdA (mapList (λ z → z) xs)) (sort-produces-sorted OrdA (mapList (λ z → z) xs))) sorted
            (nub-produces-no-dup OrdA (sort OrdA (mapList (λ z → z) xs))) noDup
            (helper' xs sorted noDup)
    
    functor-compose : {α β γ : Obj} {f : Hom α β} {g : Hom β γ} 
                    → fmap {α} {γ} (_∘_ {α} {β} {γ} g f) ≡ fmap {β} {γ} g ∘F fmap {α} {β} f
    functor-compose {α , OrdA , struct-eqA} {β , OrdB , struct-eqB} {γ , OrdC , struct-eqC} {f , tt} {g , tt} = fun-ext helper
      where
        helper' : (xs : List α) → IsSortedList OrdA xs → IsNoDupList OrdA xs 
                → nub OrdC (sort OrdC (mapList (λ z → g (f z)) xs)) ≡ nub OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs)))))
        helper' xs sorted noDup = begin
          nub OrdC (sort OrdC (mapList (λ z → g (f z)) xs))
            ≡⟨ {!!} ⟩
          nub OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f (sort OrdA xs))))))
            ≡⟨ {!!} ⟩
          nub OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f (sort OrdA xs))))))
            ≡⟨ cong (λ X → nub OrdC (sort OrdC (mapList g (nub OrdB X)))) (sort∘map∘sort≡sort∘map OrdA OrdB f xs struct-eqB) ⟩
          nub OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs))))) ∎
        
        helper : (x : ListSet (α , OrdA)) 
               → fmap {α , OrdA , struct-eqA} {γ , OrdC , struct-eqC} (g ∘F f , tt) x 
               ≡ fmap {β , OrdB , struct-eqB} {γ , OrdC , struct-eqC} (g , tt) (fmap {α , OrdA , struct-eqA} {β , OrdB , struct-eqB} (f , tt) x)
        helper (listSet xs sorted noDup) 
          = eqListSet OrdC 
            (nub OrdC (sort OrdC (mapList (λ z → g (f z)) xs))) 
            (nub OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs)))))) 
            (nub-preserves-sorted OrdC (sort OrdC (mapList (λ z → g (f z)) xs)) (sort-produces-sorted OrdC (mapList (λ z → g (f z)) xs))) 
            (nub-preserves-sorted OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs)))))
            (sort-produces-sorted OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs)))))) 
            (nub-produces-no-dup OrdC (sort OrdC (mapList (λ z → g (f z)) xs))) 
            (nub-produces-no-dup OrdC (sort OrdC (mapList g (nub OrdB (sort OrdB (mapList f xs))))))
            (helper' xs sorted noDup)
      
    unique-instances : UniqueInstances Cts
    unique-instances = proof-irr-Obj , proof-irr-Hom
      where
        proof-irr-Obj : (α : Category.Obj Hask) → ProofIrrelevance (DepObj α)
        proof-irr-Obj α (OrdA₀ , struct-eq₀) (OrdA₁ , struct-eq₁) with unique-ord-instances α OrdA₀ OrdA₁
        proof-irr-Obj α (OrdA  , struct-eq₀) (.OrdA , struct-eq₁) | refl = cong (_,_ OrdA) (proof-irr-IsStructuralEquality OrdA struct-eq₀ struct-eq₁)
        
        proof-irr-Hom : {α β : Category.Obj Hask} → (f g : α → β)
                      → (αCt : DepObj α) (βCt : DepObj β) (fCt : DepHom αCt βCt f) (gCt : DepHom αCt βCt g) 
                      → fCt ≅ gCt
        proof-irr-Hom f g αCt βCt fCt gCt = refl
