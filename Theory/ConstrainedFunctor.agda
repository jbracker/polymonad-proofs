 
module Theory.ConstrainedFunctor where

open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Level renaming ( suc to lsuc ; zero to lzero)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Haskell
open import Utilities
open import Theory.Category
open import Theory.Subcategory
open import Theory.Functor
open import Theory.Examples.Subcategory
open import Theory.Examples.Category

record ConstrainedFunctor {ℓ₀ ℓ₁ : Level} : Set (lsuc ℓ₀ ⊔ lsuc ℓ₁) where
  field
    ObjCts : Type → Set ℓ₀
    
    HomCts : {α β : Type} → ObjCts α → ObjCts β → (α → β) → Set ℓ₁
    
    _∘Ct_ : {α β γ : Type} {f : β → γ} {g : α → β} {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ}
         → HomCts β' γ' f → HomCts α' β' g → HomCts α' γ' (f ∘F g)
    
    ctId : {α : Type} {α' : ObjCts α} → HomCts α' α' idF
    
    ctAssoc : {α β γ δ : Type}
            → {α' : ObjCts α} {β' : ObjCts β} {γ' : ObjCts γ} {δ' : ObjCts δ}
            → {f : α → β} {g : β → γ} {h : γ → δ}
            → (f' : HomCts α' β' f) (g' : HomCts β' γ' g) (h' : HomCts γ' δ' h) 
            → h' ∘Ct (g' ∘Ct f') ≡ (h' ∘Ct g') ∘Ct f'
    
    ctIdR : {α β : Type} {α' : ObjCts α} {β' : ObjCts β}
          → {f : α → β} → (f' : HomCts α' β' f)
          → ctId {β} {β'} ∘Ct f' ≡ f'
    
    ctIdL : {α β : Type} {α' : ObjCts α} {β' : ObjCts β}
          → {f : α → β} → (f' : HomCts α' β' f)
          → f' ∘Ct ctId {α} {α'} ≡ f'
  
  Obj : Set (lsuc lzero ⊔ ℓ₀)
  Obj = Σ Type ObjCts
  
  Hom : Obj → Obj → Set ℓ₁
  Hom α β = Σ (proj₁ α → proj₁ β) (HomCts {proj₁ α} {proj₁ β} (proj₂ α) (proj₂ β))
  
  _∘_ : {α β γ : Obj} → Hom β γ → Hom α β → Hom α γ
  _∘_ f g = proj₁ f ∘F  proj₁ g , proj₂ f ∘Ct proj₂ g
  
  id : {α : Obj} → Hom α α
  id = idF , ctId
  
  field
    F : Obj → Type
    
    ctMap : {α β : Obj} → Hom α β → F α → F β
    
    ctFuncId : {α : Obj} → ctMap {α} {α} id ≡ idF
    
    ctFuncComp : {α β γ : Obj} {f : Hom α β} {g : Hom β γ} → ctMap (g ∘ f) ≡ ctMap g ∘F ctMap f
    
    ctObjProofIrr : {α : Type} → (αCts αCts' : ObjCts α) → αCts ≡ αCts'
    
    ctHomProofIrr : {α β : Type} {αCts : ObjCts α} {βCts : ObjCts β} {f : α → β} 
                  → (fCts fCts' : HomCts αCts βCts f) → fCts ≡ fCts'
  
  
  -- The category of constraints that restrict our constrained functor.
  ConstraintCategory : Category
  ConstraintCategory = category Obj Hom _∘_ id assoc idR idL
    where
      assoc : {α β γ δ : Obj} {f : Hom α β} {g : Hom β γ} {h : Hom γ δ} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
      assoc {α , α'} {β , β'} {γ , γ'} {δ , δ'} {f , f'} {g , g'} {h , h'} = 
        cong (λ X → h ∘F (g ∘F f) , X) (ctAssoc {α} {β} {γ} {δ} {α'} {β'} {γ'} {δ'} {f} {g} {h} f' g' h')
    
      idR : {α β : Obj} {f : Hom α β} → id ∘ f ≡ f
      idR {α , α'} {β , β'} {f , f'} = cong (λ X → f , X) (ctIdR f')
    
      idL : {α β : Obj} {f : Hom α β} → f ∘ id ≡ f
      idL {α , α'} {β , β'} {f , f'} = cong (λ X → f , X) (ctIdL f')
  
  -- The embedding of the constrained category into Haskell.
  -- Inside of Haskell the constraint information (that is lost by the embedding) 
  -- is managed by the type class system.
  EmbeddingFunctor : Functor ConstraintCategory Hask
  EmbeddingFunctor = functor proj₁ proj₁ refl refl
  
  IsInjectiveEmbedding : IsInjectiveFunctor EmbeddingFunctor
  IsInjectiveEmbedding = IsInjectiveF₀ , IsInjectiveF₁
    where
      IsInjectiveF₀ : IsInjective (Functor.F₀ EmbeddingFunctor)
      IsInjectiveF₀ (α , αCts) (.α , βCts) refl = cong (λ X → α , X) (ctObjProofIrr αCts βCts)
      
      IsInjectiveF₁ : (α β : Obj) → IsInjective (Functor.F₁ EmbeddingFunctor)
      IsInjectiveF₁ (α , αCts) (β , βCts) (f , fCts) (.f , gCts) refl = cong (λ X → f , X) (ctHomProofIrr fCts gCts)
  
  -- The actual constrained functor.
  CtFunctor : Functor ConstraintCategory Hask
  CtFunctor = functor F ctMap ctFuncId ctFuncComp
  
  -- Proof that the embedding of the 'ConstraintCategory' actually provides a subcategory of Haskell.
  ConstrainedSubcategory : Subcategory (liftCategory Hask)
  ConstrainedSubcategory = EmbeddingFunctor→LiftSubcategory EmbeddingFunctor IsInjectiveEmbedding


