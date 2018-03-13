
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Parameterized.Indexed.Applicative

open import Theory.Category.Definition
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.FromHaskellIndexedApplicative where

open Category renaming ( id to cat-id ; assoc to cat-assoc ; left-id to cat-left-id; right-id to cat-right-id )
open MonoidalCategory hiding ( Obj ; Hom )

HaskellIndexedApplicative→IndexedLaxMonoidalFunctor 
  : {ℓIxs : Level} {Ixs : Set ℓIxs} 
  → (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
  → (IndexedLaxMonoidalFunctor (Codisc Ixs) (SetMonCat {zero}) (SetMonCat {zero}))
HaskellIndexedApplicative→IndexedLaxMonoidalFunctor {ℓIxs} {Ixs} (F , applic) = indexedLaxMonoidalFunctor (λ {i j} → CatF {i} {j}) ε tensor-map assoc' left-unitality' right-unitality'
  where
    SetCat' = SetCat {zero}
    SetMonCat' = SetMonCat {zero}

    I = Codisc Ixs
    
    CatF : {i j : Obj I} → Hom I i j → Functor SetCat' SetCat'
    CatF (codisc i j) = HaskellFunctor→Functor (IxApplicative.functor applic i j)
    
    open Functor renaming ( id to fun-id )
    open IxApplicative applic renaming ( unit to ix-unit )
    open NaturalTransformation renaming ( η to nat-η )
    
    ε : (i : Obj I) → Hom SetCat' (unit SetMonCat') (F₀ (CatF (cat-id I {i})) (unit SetMonCat'))
    ε i (lift tt) = ix-unit
    
    _⊗₁F_ = _⊗₁_ SetMonCat'
    _⊗₀F_ = _⊗₀_ SetMonCat'
    _∘I_ = Category._∘_ I
    
    tensor-map : {i j k : Ixs} → (f : Hom I i j) (g : Hom I j k) → NaturalTransformation [ tensor SetMonCat' ]∘[ [ CatF f ]×[ CatF g ] ] [ CatF (g ∘I f) ]∘[ tensor SetMonCat' ]
    tensor-map ι@(codisc i j) θ@(codisc .j k) = naturalTransformation η (λ {a b} {f} → nat {a} {b} {f})
      where
        η : (x : Category.Obj (Hask ×C Hask)) → Category.Hom Hask ([ [ tensor SetMonCat' ]∘[ [ CatF ι ]×[ CatF θ ] ] ]₀ x) ([ [ CatF (θ ∘I ι) ]∘[ tensor SetMonCat' ] ]₀ x)
        η (α , β) (Fα , Fβ) = Fα ** Fβ
        
        abstract
          nat : {a b : Category.Obj (Hask ×C Hask)} {f : Category.Hom (Hask ×C Hask) a b}
              → [ [ CatF (θ ∘I ι) ]∘[ tensor SetMonCat' ] ]₁ f ∘F η a ≡ η b ∘F [ [ tensor SetMonCat' ]∘[ [ CatF ι ]×[ CatF θ ] ] ]₁ f
          nat {α₀ , α₁} {β₀ , β₁} {f₀ , f₁} = fun-ext $ λ (Fα : F i j α₀ × F j k α₁) → law-naturality f₀ f₁ (proj₁ Fα) (proj₂ Fα)
    
    abstract
      assoc' : {i j k l : Obj I} {f : Hom I i j} {g : Hom I j k} {h : Hom I k l} → (x y z : Obj SetCat') 
             → F₁ (CatF (h ∘I (g ∘I f))) (α SetMonCat' x y z) ∘F (nat-η (tensor-map (g ∘I f) h) (x ⊗₀F y , z) ∘F (nat-η (tensor-map f g) (x , y) ⊗₁F (cat-id SetCat')))
             ≅ nat-η (tensor-map f (h ∘I g)) (x , y ⊗₀F z) ∘F (cat-id SetCat' ⊗₁F (nat-η (tensor-map g h) (y , z)) ∘F (α SetMonCat (F₀ (CatF f) x) (F₀ (CatF g) y) (F₀ (CatF h) z)))
      assoc' {f = f@(codisc i j)} {g@(codisc .j k)} {h@(codisc .k l)} x y z 
        = het-fun-ext (het-fun-ext hrefl $ λ _ → hcong (λ X → F₀ (CatF {i} {l} X) (x ⊗₀F (y ⊗₀F z))) (≡-to-≅ $ cat-assoc I {f = f} {g} {h})) 
        $ λ { ((Fx , Fy) , Fz) → begin
          (F₀ (CatF (h ∘I (g ∘I f))) (x ⊗₀F (y ⊗₀F z)) ∋ 
              (F₁ (CatF (h ∘I (g ∘I f))) (α SetMonCat' x y z) ∘F (nat-η (tensor-map (g ∘I f) h) (x ⊗₀F y , z) ∘F (nat-η (tensor-map f g) (x , y) ⊗₁F (cat-id SetCat')))) ((Fx , Fy) , Fz))
            ≅⟨ ≡-to-≅ (sym (law-associativity Fx Fy Fz)) ⟩
          (F₀ (CatF (h ∘I (g ∘I f))) (x ⊗₀F (y ⊗₀F z)) ∋ (Fx ** (Fy ** Fz)))
            ≅⟨ hcong₂ (λ X Y → F₀ (CatF {i} {l} X) (x ⊗₀F (y ⊗₀F z)) ∋ Y) (≡-to-≅ $ cat-assoc I {f = f} {g} {h}) hrefl ⟩
          (F₀ (CatF ((h ∘I g) ∘I f)) (x ⊗₀F (y ⊗₀F z)) ∋ 
              (nat-η (tensor-map f (h ∘I g)) (x , y ⊗₀F z) ∘F (cat-id SetCat' ⊗₁F (nat-η (tensor-map g h) (y , z)) ∘F (α SetMonCat (F₀ (CatF f) x) (F₀ (CatF g) y) (F₀ (CatF h) z)))) ((Fx , Fy) , Fz)) ∎} 
    
    abstract
      left-unitality' : {i j : Obj I} {f : Hom I i j} (x : Obj SetCat') 
                      → λ' SetMonCat' (F₀ (CatF f) x) 
                      ≅ F₁ (CatF (f ∘I cat-id I {i})) (λ' SetMonCat' x) ∘F (nat-η (tensor-map (cat-id I {i}) f) (unit SetMonCat' , x) ∘F (ε i ⊗₁F cat-id SetCat'))
      left-unitality' {f = f@(codisc i j)} x = het-fun-ext hrefl $ λ {(Fε , Fx) → begin
        (F₀ (CatF f) x ∋ (λ' SetMonCat' (F₀ (CatF f) x)) (Fε , Fx))
          ≅⟨ ≡-to-≅ $ sym (law-left-identity' Fx) ⟩
        (F₀ (CatF f) x ∋ fmap proj₂ (ix-unit ** Fx))
          ≅⟨ hcong₂ (λ X Y → F₀ (CatF {i} {j} X) x ∋ Y) (≡-to-≅ (sym (cat-left-id I {f = f}))) hrefl ⟩
        (F₀ (CatF (f ∘I cat-id I {i})) x ∋ fmap proj₂ (ε i Fε ** Fx))
          ≅⟨ hrefl ⟩
        (F₀ (CatF (f ∘I cat-id I {i})) x ∋ (F₁ (CatF (f ∘I cat-id I {i})) (λ' SetMonCat' x) ∘F (nat-η (tensor-map (cat-id I {i}) f) (unit SetMonCat' , x) ∘F (ε i ⊗₁F cat-id SetCat'))) (Fε , Fx)) ∎ } 
    
    abstract
      right-unitality' : {i j : Ixs} {f : Hom I i j} (x : Obj SetCat') 
                       → ρ SetMonCat' (F₀ (CatF f) x) 
                       ≅ F₁ (CatF (cat-id I {j} ∘I f)) (ρ SetMonCat' x) ∘F (nat-η (tensor-map f (cat-id I {j})) (x , unit SetMonCat') ∘F (cat-id SetCat' ⊗₁F ε j))
      right-unitality' {f = f@(codisc i j)} x = het-fun-ext hrefl $ λ {(Fx , Fε) → begin
        (F₀ (CatF f) x ∋ (ρ SetMonCat' (F₀ (CatF f) x)) (Fx , Fε))
          ≅⟨ ≡-to-≅ $ sym (law-right-identity' Fx) ⟩
        (F₀ (CatF f) x ∋ fmap proj₁ (Fx ** ix-unit))
          ≅⟨ hcong₂ (λ X Y → F₀ (CatF {i} {j} X) x ∋ Y) (≡-to-≅ (sym (cat-right-id I {f = f}))) hrefl ⟩
        (F₀ (CatF (cat-id I {j} ∘I f)) x ∋ fmap proj₁ (Fx ** ε j Fε))
          ≅⟨ hrefl ⟩
        (F₀ (CatF (cat-id I {j} ∘I f)) x ∋ (F₁ (CatF (cat-id I {j} ∘I f)) (ρ SetMonCat' x) ∘F (nat-η (tensor-map f (cat-id I {j})) (x , unit SetMonCat') ∘F (cat-id SetCat' ⊗₁F ε j))) (Fx , Fε)) ∎ } 

