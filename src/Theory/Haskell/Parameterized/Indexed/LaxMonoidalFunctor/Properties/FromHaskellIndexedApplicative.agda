
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.Indexed.Applicative

open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.FromHaskellIndexedApplicative where

-- open Category hiding ( Obj ; Hom )
open MonoidalCategory renaming ( id to cat-id )

HaskellIndexedApplicative→IndexedLaxMonoidalFunctor 
  : {ℓIxs : Level} {Ixs : Set ℓIxs} 
  → (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
  → (IndexedLaxMonoidalFunctor Ixs (SetMonCat {zero}) (SetMonCat {zero}))
HaskellIndexedApplicative→IndexedLaxMonoidalFunctor {ℓIxs} {Ixs} (F , applic) = indexedLaxMonoidalFunctor CatF ε tensor-map assoc' left-unitality' right-unitality'
  where
    SetMonCat' = SetMonCat {zero}
    
    CatF : (i j : Ixs) → Functor Hask Hask
    CatF i j = HaskellFunctor→Functor (IxApplicative.functor applic i j)
    
    open Functor renaming ( id to fun-id )
    open IxApplicative applic renaming ( unit to ix-unit )
    open NaturalTransformation renaming ( η to nat-η )
    
    ε : (i : Ixs) → Hom SetMonCat' (unit SetMonCat') (F₀ (CatF i i) (unit SetMonCat'))
    ε i (lift tt) = ix-unit
    
    _⊗₁F_ = _⊗₁_ SetMonCat'
    _⊗₀F_ = _⊗₀_ SetMonCat'
    
    tensor-map : (i j k : Ixs) → NaturalTransformation [ tensor SetMonCat' ]∘[ [ CatF i j ]×[ CatF j k ] ] [ CatF i k ]∘[ tensor SetMonCat' ]
    tensor-map i j k = naturalTransformation η (λ {a b} {f} → nat {a} {b} {f})
      where
        η : (x : Category.Obj (Hask ×C Hask)) → Category.Hom Hask ([ [ tensor SetMonCat' ]∘[ [ CatF i j ]×[ CatF j k ] ] ]₀ x) ([ [ CatF i k ]∘[ tensor SetMonCat' ] ]₀ x)
        η (α , β) (Fα , Fβ) = Fα ** Fβ
        
        abstract
          nat : {a b : Category.Obj (Hask ×C Hask)} {f : Category.Hom (Hask ×C Hask) a b}
              → [ [ CatF i k ]∘[ tensor SetMonCat' ] ]₁ f ∘F η a ≡ η b ∘F [ [ tensor SetMonCat' ]∘[ [ CatF i j ]×[ CatF j k ] ] ]₁ f
          nat {α₀ , α₁} {β₀ , β₁} {f₀ , f₁} = fun-ext $ λ (Fα : F i j α₀ × F j k α₁) → law-naturality f₀ f₁ (proj₁ Fα) (proj₂ Fα)
    
    abstract
      assoc' : {i j k l : Ixs} (x y z : Obj SetMonCat) 
             → F₁ (CatF i l) (α SetMonCat x y z) ∘F (nat-η (tensor-map i k l) (x ⊗₀F y , z) ∘F (nat-η (tensor-map i j k) (x , y) ⊗₁F (cat-id SetMonCat')))
             ≡ nat-η (tensor-map i j l) (x , (SetMonCat ⊗₀ y) z) ∘F ((SetMonCat ⊗₁ cat-id SetMonCat) (nat-η (tensor-map j k l) (y , z)) ∘F (α SetMonCat (F₀ (CatF i j) x) (F₀ (CatF j k) y) (F₀ (CatF k l) z)))
      assoc' x y z = fun-ext $ λ {((Fx , Fy) , Fz) → sym $ law-associativity Fx Fy Fz }
    
    abstract
      left-unitality' : {i j : Ixs} (x : Obj SetMonCat') 
                      → λ' SetMonCat' (F₀ (CatF i j) x) 
                      ≡ F₁ (CatF i j) (λ' SetMonCat' x) ∘F (nat-η (tensor-map i i j) (unit SetMonCat' , x) ∘F (ε i ⊗₁F cat-id SetMonCat'))
      left-unitality' x = fun-ext $ λ {(Fε , Fx) → sym $ law-left-identity' Fx}
    
    abstract
      right-unitality' : {i j : Ixs} (x : Obj SetMonCat) 
                       → ρ SetMonCat' (F₀ (CatF i j) x) 
                       ≡ F₁ (CatF i j) (ρ SetMonCat' x) ∘F (nat-η (tensor-map i j j) (x , unit SetMonCat') ∘F (cat-id SetMonCat ⊗₁F ε j))
      right-unitality' x = fun-ext $ λ {(Fx , Fε) → sym $ law-right-identity' Fx}
