
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)

open import Data.Unit hiding ( _≤_ ; _≟_ ; total )
open import Data.Empty
open import Data.List
open import Data.Product hiding ( map )

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( refl ; _≅_ ; ≡-to-≅ )

open import Extensionality
open import Equality
open import ProofIrrelevance
open import Haskell hiding ( Type )

open import Theory.Category
open import Theory.Category.Dependent
open import Theory.Category.Concrete

open import Theory.Haskell.Constrained
open import Theory.Haskell.Constrained.Functor
open import Theory.Haskell.Constrained.Examples.SetFunctor.Base
open import Theory.Haskell.Constrained.Examples.SetFunctor.Insert
open import Theory.Haskell.Constrained.Examples.SetFunctor.Map

module Theory.Haskell.Constrained.Examples.SetFunctor where 

open ≡-Reasoning

mapList-id : {ℓ ℓEq ℓOrd : Level}
           → {A : Set ℓ} {OrdA : OrdInstance {ℓ} {ℓEq} {ℓOrd} A} 
           → (xs : List A) → IsSortedNoDupList OrdA xs
           → mapList {OrdA = OrdA} {OrdA} (λ x → x) xs ≡ xs
mapList-id [] (lift tt) = refl
mapList-id (x ∷ xs) (allX , sortedX) = begin
  insert x (mapList (λ a → a) xs) 
    ≡⟨ cong (insert x) (mapList-id xs sortedX) ⟩
  insert x xs
    ≡⟨ insert-adds-in-front allX ⟩
  x ∷ xs ∎

mapList-compose : {ℓA ℓB ℓC ℓEqA ℓEqB ℓEqC ℓOrdA ℓOrdB ℓOrdC : Level}
                → {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
                → {OrdA : OrdInstance {ℓA} {ℓEqA} {ℓOrdA} A} {OrdB : OrdInstance {ℓB} {ℓEqB} {ℓOrdB} B} {OrdC : OrdInstance {ℓC} {ℓEqC} {ℓOrdC} C}
                → IsStructuralEquality OrdB → IsStructuralEquality OrdC
                → (f : A → B) → (g : B → C) → (xs : List A)
                → mapList {OrdA = OrdA} {OrdC} (g ∘F f) xs ≡ mapList {OrdA = OrdB} {OrdC} g (mapList {OrdA = OrdA} {OrdB} f xs)
mapList-compose struct-eqB struct-eqC f g [] = refl
mapList-compose {OrdA = OrdA} struct-eqB struct-eqC f g (x ∷ xs) = begin
  insert (g (f x)) (mapList (g ∘F f) xs)
    ≡⟨ cong (insert (g (f x))) (mapList-compose {OrdA = OrdA} struct-eqB struct-eqC f g xs) ⟩
  insert (g (f x)) (mapList g (mapList f xs))
    ≡⟨ sym (map-insert-commute g (f x) (mapList f xs) struct-eqB struct-eqC) ⟩
  mapList g (insert (f x) (mapList f xs)) ∎

FunctorLSet : {ℓ : Level} → ConstrainedFunctor {ℓ}
FunctorLSet {ℓ} = record
  { Cts = CtCat
  ; F = F
  ; map = λ {α} {β} → fmap {α} {β}
  ; functor-id = λ {α} → functor-id {α}
  ; functor-compose = λ {α} {β} {γ} {f} {g} → functor-compose {α} {β} {γ} {f} {g}
  } where
    Type = Set ℓ
    open import Theory.Haskell.Constrained {ℓ}
    
    ObjCt : Set ℓ → Set (lsuc ℓ)
    ObjCt A = Σ (OrdInstance {ℓ} {lzero} {lzero} A) IsStructuralEquality
    
    HomCt : {A B : Type} → ObjCt A → ObjCt B → (A → B) → Set lzero
    HomCt OrdA OrdB f = ⊤
    
    CtCat = dependentCategory ObjCt HomCt (λ _ _ → tt) tt (λ f' g' h' → refl) (λ f' → refl) (λ f' → refl)
    
    open DependentCategory CtCat using ( DepCat )
    open Category DepCat
    
    Obj' : Obj → Σ Type (OrdInstance {ℓ} {lzero} {lzero})
    Obj' (A , OrdA , _) = (A , OrdA)

    F : Obj → Category.Obj Hask
    F A = LSet (Obj' A)
    
    fmap : {A B : Obj} → Σ (proj₁ A → proj₁ B) (HomCt (proj₂ A) (proj₂ B)) → F A → F B
    fmap (f , tt) set = mapSet f set
    
    open ≡-Reasoning
    
    functor-id : {A : Obj} → fmap {A} {A} (id {A}) ≡ idF
    functor-id {A} = fun-ext helper
      where
        helper : (x : LSet (Obj' A)) → fmap {A} {A} (id {A}) x ≡ idF x
        helper (lset [] sorted) = refl
        helper (lset (x ∷ xs) (allX , sortedX)) = lset-eq _ (x ∷ xs) _ (allX , sortedX) $ begin
          insert {OrdA = proj₂ (Obj' A)} x (LSet.xs (mapSet (λ a → a) (lset xs sortedX)))
            ≡⟨ cong (insert {OrdA = proj₂ (Obj' A)} x) (map-structure (λ a → a) (lset xs sortedX)) ⟩
          insert {OrdA = proj₂ (Obj' A)} x (mapList {OrdA = proj₂ (Obj' A)} {proj₂ (Obj' A)} (λ a → a) xs)
            ≡⟨ cong (insert {OrdA = proj₂ (Obj' A)} x) (mapList-id xs sortedX) ⟩
          insert {OrdA = proj₂ (Obj' A)} x xs
            ≡⟨ insert-adds-in-front allX ⟩
          x ∷ xs ∎
    
    functor-compose : {α β γ : Obj}
                    → {f : Hom α β} {g : Hom β γ} 
                    → fmap {α} {γ} (_∘_ {α} {β} {γ} g f) ≡ fmap {β} {γ} g ∘F fmap {α} {β} f
    functor-compose {A , OrdA , struct-eqA} {B , OrdB , struct-eqB} {C , OrdC , struct-eqC} {f , tt} {g , tt} = fun-ext (λ xs → helper xs)
      where
        ObjA = A , OrdA , struct-eqA
        ObjB = B , OrdB , struct-eqB
        ObjC = C , OrdC , struct-eqC
        
        helper : (set : LSet (A , OrdA)) → fmap {ObjA} {ObjC} (g ∘F f , tt) set ≡ fmap {ObjB} {ObjC} (g , tt) (fmap {ObjA} {ObjB} (f , tt) set)
        helper (lset [] (lift tt)) = refl
        helper (lset (x ∷ xs) (allX , sortedX)) = lset-eq _ _ _ _ $ begin
          insert ((g ∘F f) x) (LSet.xs (mapSet (g ∘F f) (lset xs sortedX)))
            ≡⟨ cong (insert (g (f x))) (map-structure (g ∘F f) (lset xs sortedX)) ⟩
          insert (g (f x)) (mapList (g ∘F f) xs)
            ≡⟨ cong (insert (g (f x))) (mapList-compose {OrdA = OrdA} struct-eqB struct-eqC f g xs) ⟩
          insert (g (f x)) (mapList g (mapList f xs))
            ≡⟨ sym (map-insert-commute g (f x) (mapList f xs) struct-eqB struct-eqC) ⟩
          mapList g (insert (f x) (mapList f xs))
            ≡⟨ cong (mapList g ∘F insert (f x)) (sym (map-structure f (lset xs sortedX))) ⟩
          mapList g (insert (f x) (LSet.xs (mapSet f (lset xs sortedX))))
            ≡⟨ sym (map-structure g (lset (insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))) (insert-preserves-IsSortedNoDupList (LSet.sorted (mapSet f (lset xs sortedX)))))) ⟩
          LSet.xs (mapSet g (lset (insert (f x) (LSet.xs (mapSet f (lset xs sortedX)))) (insert-preserves-IsSortedNoDupList (LSet.sorted (mapSet f (lset xs sortedX)))))) ∎


FunctorLSet-DependentHomUniqueness : {ℓ : Level} → DependentHomUniqueness (ConstrainedFunctor.Cts (FunctorLSet {ℓ}))
FunctorLSet-DependentHomUniqueness (f₁ , tt) (.f₁ , tt) refl = refl

FunctorLSet-DependentObjUniqueness : {ℓ : Level} 
                                   → ((A : Set ℓ) → ProofIrrelevance (OrdInstance {ℓ} {lzero} {lzero} A)) 
                                   → DependentObjUniqueness (ConstrainedFunctor.Cts (FunctorLSet {ℓ}))
FunctorLSet-DependentObjUniqueness proof-irr-Ord (a₁ , ord-a₂ , struct-eq-a₂) (.a₁ , ord-b₂ , struct-eq-b₂) refl with proof-irr-Ord a₁ ord-a₂ ord-b₂ 
FunctorLSet-DependentObjUniqueness proof-irr-Ord (a₁ , ord-a , struct-eq-a₂) (.a₁ , .ord-a , struct-eq-b₂) refl | refl 
  = ≡-to-≅ (cong (_,_ ord-a) (proof-irr-IsStructuralEquality ord-a struct-eq-a₂ struct-eq-b₂))

FunctorLSet-UniqueInstances : {ℓ : Level}
                            → ((A : Set ℓ) → ProofIrrelevance (OrdInstance {ℓ} {lzero} {lzero} A))
                            → UniqueInstances (ConstrainedFunctor.Cts (FunctorLSet {ℓ}))
FunctorLSet-UniqueInstances {ℓ} proof-irr-ord = unique-type-inst , unique-hom-inst
  where
    open DependentCategory (ConstrainedFunctor.Cts FunctorLSet)
    open Category DepCat

    Type = Set ℓ
    
    unique-type-inst : (α : Type) → (αCts αCts' : DepObj α) → αCts ≡ αCts'
    unique-type-inst α (ordA , struct-eqA) (ordB , struct-eqB) with proof-irr-ord α ordA ordB
    unique-type-inst α (ord , struct-eqA) (.ord , struct-eqB) | refl 
      = cong (_,_ ord) (proof-irr-IsStructuralEquality ord struct-eqA struct-eqB)
    
    unique-hom-inst : {α β : Type} → (f g : α → β)
                    → (αCt : DepObj α) → (βCt : DepObj β) 
                    → (fCt : DepHom αCt βCt f) → (gCt : DepHom αCt βCt g)
                    → fCt ≅ gCt
    unique-hom-inst f g a b tt tt = refl

FunctorLSetCodomain-IsConcreteCategory : {ℓ : Level} → IsConcreteCategory (DependentCategory.DepCat (ConstrainedFunctor.Cts (FunctorLSet {ℓ})))
FunctorLSetCodomain-IsConcreteCategory {ℓ} = ConstraintCategory→ConcreteCategory (ConstrainedFunctor.Cts FunctorLSet) (λ {a} {b} → FunctorLSet-DependentHomUniqueness {ℓ} {a} {b})

