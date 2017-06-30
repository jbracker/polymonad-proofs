
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative

open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation

module Theory.Functor.Monoidal.Properties.FromHaskellApplicative where

open Category hiding ( Obj ; Hom )
open MonoidalCategory

HaskellApplicative→LaxMonoidalFunctor
  : {F : TyCon}
  → Applicative F
  → LaxMonoidalFunctor (setMonoidalCategory {zero}) (setMonoidalCategory {zero})
HaskellApplicative→LaxMonoidalFunctor {F} applic = laxMonoidalFunctor CatF ε tensor-map {!!} {!!} {!!}
  where
    MonHask = setMonoidalCategory {zero}
    
    CatF : Functor Hask Hask
    CatF = HaskellFunctor→Functor (Applicative.functor applic)
    
    open Functor CatF
    open Applicative applic hiding ( unit )
    
    ε : Hom MonHask (unit MonHask) (F₀ (unit MonHask))
    ε u = F₁ lift (Applicative.unit applic)
    
    tensor-map : NaturalTransformation [ tensor MonHask ]∘[ [ CatF ]×[ CatF ] ] [ CatF ]∘[ tensor MonHask ]
    tensor-map = naturalTransformation η (λ {a b} {f} → nat {a} {b} {f})
      where
        η : (x : Category.Obj (Hask ×C Hask)) → Category.Hom Hask ([ [ tensor MonHask ]∘[ [ CatF ]×[ CatF ] ] ]₀ x) ([ [ CatF ]∘[ tensor MonHask ] ]₀ x)
        η (α , β) (Fα , Fβ) = Fα ** Fβ
        
        nat : {a b : Category.Obj (Hask ×C Hask)} {f : Category.Hom (Hask ×C Hask) a b}
            → [ [ CatF ]∘[ tensor MonHask ] ]₁ f ∘F η a ≡ η b ∘F [ [ tensor MonHask ]∘[ [ CatF ]×[ CatF ] ] ]₁ f
        nat {α₀ , α₁} {β₀ , β₁} {f₀ , f₁} = fun-ext $ λ (Fα : F α₀ × F α₁) → law-naturality f₀ f₁ (proj₁ Fα) (proj₂ Fα)
