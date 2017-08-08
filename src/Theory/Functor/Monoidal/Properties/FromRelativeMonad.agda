
open import Level
open import Function hiding ( id )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Theory.Category.Definition
open import Theory.Category.Dependent
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Dependent
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Monad.Relative

open import Haskell.Applicative using ( _***_ )

open import Equality
open import Extensionality

module Theory.Functor.Monoidal.Properties.FromRelativeMonad where

open Category hiding ( _∘_ )
open DependentMonoidalCategory

RelativeMonad→LaxMonoidalFunctor : {ℓ ℓCt₀ ℓCt₁ : Level}
                                 → {CtMonCat : DependentMonoidalCategory {ℓDep₀ = ℓCt₀} {ℓDep₁ = ℓCt₁} (SetMonCat {ℓ})}
                                 → {T : Obj (DependentMonoidalCategory.DepCat CtMonCat) → Obj (SetCat {ℓ})}
                                 → RelativeMonad T (forgetful-functor CtMonCat)
                                 → LaxMonoidalFunctor (DepMonCat CtMonCat) (SetMonCat {ℓ})
RelativeMonad→LaxMonoidalFunctor {ℓ} {ℓCt₀} {ℓCt₁} {CtMonCat} {T} monad
  = laxMonoidalFunctor FunctorT unit-map ap-map {!!} {!!} {!!}
  where
    open RelativeMonad monad
    open Functor FunctorT
    open MonoidalCategory hiding ( Hom ; _∘_ )

    unit-map : MonoidalCategory.Hom SetMonCat (unit SetMonCat) (F₀ (unit (DepMonCat CtMonCat)))
    unit-map (lift tt) = η (lift tt)

    _⊗Dep₀_ = _Dep⊗₀_ CtMonCat
    _⊗Dep₁_ = _Dep⊗₁_ CtMonCat

    ap-map : NaturalTransformation [ tensor SetMonCat ]∘[ [ FunctorT ]×[ FunctorT ] ] [ FunctorT ]∘[ tensor (DepMonCat CtMonCat) ]
    ap-map = naturalTransformation η-map η-nat
      where
        η-map : (x : Obj (DepCat CtMonCat) × Obj (DepCat CtMonCat))
              → (T (proj₁ x) × T (proj₂ x))
              → T ([ tensor (DepMonCat CtMonCat) ]₀ x)
        η-map ((α , ct-α) , (β , ct-β)) (Fa , Fb) = kext (λ a → kext (η ∘ (λ b → (a , b))) Fb) Fa
        -- We write this using only kext and η instead of with kext and the FunctorT mapping.
        -- But that is not a problem, because by "functor-kext-coher": [ FunctorT ]₁ f ≡ kext (η ∘D [ forgetful-functor CtMonCat ]₁ f)
        -- With f = λ b → (a , b)

        η-nat : {a b : Obj (DepCat CtMonCat) × Obj (DepCat CtMonCat)}
              → {f : Hom (DepCat CtMonCat ×C DepCat CtMonCat) a b}
              → [ [ FunctorT ]∘[ tensor (DepMonCat CtMonCat) ] ]₁ f ∘ η-map a
              ≡ η-map b ∘ [ [ tensor SetMonCat ]∘[ [ FunctorT ]×[ FunctorT ] ] ]₁ f
        η-nat {(α , ct-α) , (γ , ct-γ)} {(β , ct-β) , (δ , ct-δ)} {(f , ct-f) , (g , ct-g)} = fun-ext $ λ {(Fa , Fb) → begin
          ( [ [ FunctorT ]∘[ tensor (DepMonCat CtMonCat) ] ]₁ ((f , ct-f) , (g , ct-g)) ∘ η-map ((α , ct-α) , (γ , ct-γ)) ) (Fa , Fb)
            ≡⟨⟩
          ( [ FunctorT ]₁ (f *** g , ct-f ⊗Dep₁ ct-g) ) (kext (λ a → kext (η ∘ (λ b → (a , b))) Fb) Fa)
            ≡⟨⟩
          (kext (η ∘ (f *** g)) ∘ kext (λ a → kext (η ∘ (λ b → (a , b))) Fb)) Fa
            ≡⟨ cong (λ X → X Fa) (sym coher) ⟩
          kext (λ a → (kext (η ∘ (f *** g)) ∘ kext (η ∘ (λ b → (a , b)))) Fb) Fa
            ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ a → cong (λ X → X Fb) (sym coher))) ⟩
          kext (λ a → kext (kext (η ∘ (f *** g)) ∘ (η ∘ (λ b → (a , b)))) Fb) Fa
            ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ a → cong (λ X → kext (X ∘ (λ b → a , b)) Fb) (RelativeMonad.right-id monad))) ⟩
          kext (λ a → kext ((η ∘ (f *** g)) ∘ (λ b → (a , b))) Fb) Fa
            ≡⟨⟩
          kext (λ a → kext ((η ∘ (λ b → (f a , b))) ∘ g) Fb) Fa
            ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ a → cong (λ X → kext (X ∘ g) Fb) (sym $ RelativeMonad.right-id monad) )) ⟩
          kext (λ a → kext (kext (η ∘ (λ b → (f a , b))) ∘ (η ∘ g)) Fb) Fa
            ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ a → cong (λ X → X Fb) coher)) ⟩
          kext (λ a → (kext (η ∘ (λ b → (f a , b))) ∘ kext (η ∘ g)) Fb) Fa
            ≡⟨⟩
          kext (λ a → kext (η ∘ (λ b → (f a , b))) (kext (η ∘ g) Fb)) Fa
            ≡⟨⟩
          kext ((λ a → kext (η ∘ (λ b → (a , b))) (kext (η ∘ g) Fb)) ∘ f) Fa
            ≡⟨ cong (λ X → kext (X ∘ f) Fa) (sym $ RelativeMonad.right-id monad) ⟩
          kext ((kext (λ a → kext (η ∘ (λ b → (a , b))) (kext (η ∘ g) Fb)) ∘ η) ∘ f) Fa
            ≡⟨ cong (λ X → X Fa) coher ⟩
          (kext (λ a → kext (η ∘ (λ b → (a , b))) (kext (η ∘ g) Fb)) ∘ kext (η ∘ f)) Fa
            ≡⟨⟩
          kext (λ a → kext (η ∘ (λ b → (a , b))) (kext (η ∘ g) Fb)) (kext (η ∘ f) Fa)
            ≡⟨⟩
          kext (λ a → kext (η ∘ (λ b → (a , b))) (F₁ (g , ct-g) Fb)) (F₁ (f , ct-f) Fa)
            ≡⟨⟩
          ( η-map ((β , ct-β) , (δ , ct-δ)) ∘ (λ x → x) ) (F₁ (f , ct-f) Fa , F₁ (g , ct-g) Fb)
            ≡⟨ cong (λ X → ( η-map ((β , ct-β) , (δ , ct-δ)) ∘ X ) (F₁ (f , ct-f) Fa , F₁ (g , ct-g) Fb)) (sym (Functor.id (tensor SetMonCat))) ⟩
          ( η-map ((β , ct-β) , (δ , ct-δ)) ∘ [ tensor SetMonCat ]₁ ((λ x → x) , (λ x → x)) ) (F₁ (f , ct-f) Fa , F₁ (g , ct-g) Fb)
            ≡⟨⟩
          ( η-map ((β , ct-β) , (δ , ct-δ)) ∘ [ [ tensor SetMonCat ]∘[ [ FunctorT ]×[ FunctorT ] ] ]₁ ((f , ct-f) , (g , ct-g)) ) (Fa , Fb) ∎ }
