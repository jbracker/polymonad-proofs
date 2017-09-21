
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
  = laxMonoidalFunctor FunctorT unit-map ap-map assoc' left-unital right-unital
  where
    open RelativeMonad monad
    open Functor FunctorT
    open MonoidalCategory renaming ( Obj to MObj ; Hom to MHom ) hiding ( _∘_ )
    open NaturalTransformation renaming ( η to nat-η )

    unit-map : MonoidalCategory.Hom SetMonCat (unit SetMonCat) (F₀ (unit (DepMonCat CtMonCat)))
    unit-map (lift tt) = η (lift tt)

    _⊗Dep₀_ = _Dep⊗₀_ CtMonCat
    _⊗Dep₁_ = _Dep⊗₁_ CtMonCat
    
    ap-map : NaturalTransformation [ tensor SetMonCat ]∘[ [ FunctorT ]×[ FunctorT ] ] [ FunctorT ]∘[ tensor (DepMonCat CtMonCat) ]
    ap-map = naturalTransformation η-map (λ {a b} {f} → η-nat {a} {b} {f})
      where
        η-map : (x : Obj (DepCat CtMonCat) × Obj (DepCat CtMonCat))
              → (T (proj₁ x) × T (proj₂ x))
              → T ([ tensor (DepMonCat CtMonCat) ]₀ x)
        η-map ((α , ct-α) , (β , ct-β)) (Fa , Fb) = kext (λ a → kext (η ∘ (λ b → (a , b))) Fb) Fa
        -- We write this using only kext and η instead of with kext and the FunctorT mapping.
        -- But that is not a problem, because by "functor-kext-coher": [ FunctorT ]₁ f ≡ kext (η ∘D [ forgetful-functor CtMonCat ]₁ f)
        -- With f = λ b → (a , b)
        
        abstract
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
    
    abstract
      kext-compose : {α β γ : MObj (DepMonCat CtMonCat)} {f : proj₁ α → proj₁ β} {g : proj₁ β → proj₁ γ} 
                   → kext {a = α} (η {a = γ} ∘ (g ∘ f)) ≡ kext {a = β} (η ∘ g) ∘ kext (η ∘ f)
      kext-compose {α} {β} {γ} {f} {g} = begin
        kext {a = α} (η {a = γ} ∘ (g ∘ f))
          ≡⟨⟩
        kext {a = α} ((η {a = γ} ∘ g) ∘ f)
          ≡⟨ cong (λ X → kext {a = α} (X ∘ f)) (sym $ RelativeMonad.right-id monad) ⟩
        kext {a = α} ((kext {a = β} (η {a = γ} ∘ g) ∘ η {a = β}) ∘ f)
          ≡⟨⟩
        kext {a = α} (kext {a = β} (η {a = γ} ∘ g) ∘ (η {a = β} ∘ f))
          ≡⟨ RelativeMonad.coher monad ⟩
        kext {a = β} (η ∘ g) ∘ kext (η ∘ f) ∎
    
    abstract
      assoc' : (x y z : MObj (DepMonCat CtMonCat)) 
             → F₁ (α (DepMonCat CtMonCat) x y z) ∘ (nat-η ap-map ((DepMonCat CtMonCat ⊗₀ x) y , z) ∘ (nat-η ap-map (x , y) *** (λ x → x)))
             ≡ nat-η ap-map (x , (DepMonCat CtMonCat ⊗₀ y) z) ∘ (((λ x → x) *** nat-η ap-map (y , z)) ∘ (α SetMonCat (F₀ x) (F₀ y) (F₀ z)))
      assoc' (α , ct-α) (β , ct-β) (γ , ct-γ) = fun-ext $ λ {((Fa , Fb) , Fc) → begin
        kext (η ∘ (λ {((a , b) , c) → (a , (b , c))})) (kext (λ a → kext (η ∘ (λ b → (a , b))) Fc) (kext (λ a → kext (η ∘ (λ b → (a , b))) Fb) Fa))
          ≡⟨ cong (λ X → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))})) (X Fa)) (sym $ RelativeMonad.coher monad) ⟩
        kext (η ∘ (λ {((a , b) , c) → (a , (b , c))})) (kext ((kext (λ a → kext (η ∘ (λ b → (a , b))) Fc)) ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fb)) Fa)
          ≡⟨ cong (λ X → X Fa) (sym $ RelativeMonad.coher monad) ⟩
        kext ((kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}))) ∘ ((kext (λ a → kext (η ∘ (λ b → (a , b))) Fc)) ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fb))) Fa
          ≡⟨ cong (λ X → kext (X ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fb)) Fa) (sym $ RelativeMonad.coher monad) ⟩
        kext (kext (kext (η ∘ (λ {((a , b) , c) → (a , (b , c))})) ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fc)) ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fb)) Fa
          ≡⟨⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))})) (kext (η ∘ (λ b → (e , b))) Fc)) (kext (η ∘ (λ b → (d , b))) Fb)) Fa
          ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ d → cong (λ X → kext X (kext (η {a = (α × β) , ct-α ⊗Dep₀ ct-β} ∘ (λ b → (d , b))) Fb)) (fun-ext (λ e → cong (λ X → X Fc) (sym kext-compose))))) ⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}) ∘ (λ b → (e , b))) Fc) (kext (η ∘ (λ b → (d , b))) Fb)) Fa
          ≡⟨⟩
        kext (λ d → (kext (λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}) ∘ (λ b → (e , b))) Fc) ∘ kext (η ∘ (λ b → (d , b)))) Fb) Fa
          ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ d → cong (λ X → X Fb) (sym $ RelativeMonad.coher monad))) ⟩
        kext (λ d → (kext (kext (λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}) ∘ (λ b → (e , b))) Fc) ∘ (η ∘ (λ b → (d , b)))) Fb)) Fa
          ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ d → cong (λ X → kext (X ∘ (λ b → (d , b))) Fb) (RelativeMonad.right-id monad))) ⟩
        kext (λ d → (kext ((λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}) ∘ (λ b → (e , b))) Fc) ∘ (λ b → (d , b))) Fb)) Fa
          ≡⟨⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ {((a , b) , c) → (a , (b , c))}) ∘ (λ b → ((d , e) , b))) Fc) Fb) Fa
          ≡⟨⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ b → (d , (e , b)))) Fc) Fb) Fa
          ≡⟨⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ b → (d , b)) ∘ (λ b → (e , b))) Fc) Fb) Fa
          ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ d → cong (λ X → kext X Fb) (fun-ext (λ e → cong (λ X → X Fc) kext-compose)))) ⟩
        kext (λ d → kext (λ e → kext (η ∘ (λ b → (d , b))) (kext (η ∘ (λ b → (e , b))) Fc)) Fb) Fa
          ≡⟨⟩
        kext (λ d → kext (kext (η ∘ (λ b → (d , b))) ∘ (λ a → kext (η ∘ (λ b → (a , b))) Fc)) Fb) Fa
          ≡⟨ cong (λ X → kext X Fa) (fun-ext (λ a → cong (λ X → X Fb) (RelativeMonad.coher monad))) ⟩
        kext (λ a → kext (η ∘ (λ b → (a , b))) (kext (λ a → kext (η ∘ (λ b → (a , b))) Fc) Fb)) Fa ∎ }

    abstract
      left-unital : (x : MObj (DepMonCat CtMonCat)) 
                  → proj₂ 
                  ≡ F₁ (λ' (DepMonCat CtMonCat) x) ∘ (nat-η ap-map (unit (DepMonCat CtMonCat) , x) ∘ (unit-map *** (λ x → x)))
      left-unital (α , ct-α) = fun-ext $ λ {(lift tt , Fa) → begin
        Fa 
          ≡⟨ cong (λ X → X Fa) $ sym $ RelativeMonad.left-id monad ⟩ 
        kext η Fa
          ≡⟨⟩ 
        kext ((η ∘ proj₂ {a = ℓCt₀}) ∘ (λ b → (lift tt , b))) Fa
          ≡⟨ cong (λ X → kext (X ∘ (λ b → (lift tt , b))) Fa) (sym $ RelativeMonad.right-id monad) ⟩ 
        kext (kext (η ∘ proj₂) ∘ (η ∘ (λ b → (lift tt , b)))) Fa
          ≡⟨ cong (λ X → X Fa) (RelativeMonad.coher monad) ⟩ 
        kext (η ∘ proj₂) ( kext (η ∘ (λ b → (lift tt , b))) Fa )
          ≡⟨⟩ 
        kext (η ∘ proj₂) ( (λ a → kext (η ∘ (λ b → (a , b))) Fa) (lift tt) )
          ≡⟨ cong (λ X → kext (η ∘ proj₂) (X (lift tt))) (sym $ RelativeMonad.right-id monad) ⟩ 
        kext (η ∘ proj₂) ( kext (λ a → kext (η ∘ (λ b → (a , b))) Fa) (η (lift tt)) )  ∎ }
    
    abstract
      right-unital : (x : MObj (DepMonCat CtMonCat)) 
                   → proj₁
                   ≡ F₁ (ρ (DepMonCat CtMonCat) x) ∘ (nat-η ap-map (x , unit (DepMonCat CtMonCat)) ∘ ((λ x → x) *** unit-map))
      right-unital (α , ct-α) = fun-ext $ λ {(Fa , lift tt) → begin
        Fa
          ≡⟨ cong (λ X → X Fa) (sym $ RelativeMonad.left-id monad) ⟩
        kext η Fa
          ≡⟨⟩
        kext ( (η ∘ proj₁ {b = ℓCt₀}) ∘ (λ a → (a , lift tt)) ) Fa
          ≡⟨ cong (λ X → kext (X ∘ (λ a → (a , lift tt))) Fa) (sym $ RelativeMonad.right-id monad) ⟩
        kext ( (kext (η ∘ proj₁)) ∘ (η ∘ (λ a → (a , lift tt))) ) Fa
          ≡⟨⟩
        kext ( (kext (η ∘ proj₁)) ∘ (λ a → η (a , lift tt)) ) Fa
          ≡⟨⟩
        kext ( (kext (η ∘ proj₁)) ∘ (λ a → (η ∘ (λ b → (a , b))) (lift tt) ) ) Fa
          ≡⟨ cong (λ X → X Fa) (RelativeMonad.coher monad) ⟩
        kext (η ∘ proj₁) (kext (λ a → (η ∘ (λ b → (a , b))) (lift tt) ) Fa)
          ≡⟨ cong (λ X → kext (η ∘ proj₁) (kext X Fa)) (fun-ext (λ a → cong (λ X → X (lift tt)) (sym $ RelativeMonad.right-id monad))) ⟩
        kext (η ∘ proj₁) (kext (λ a → kext (η ∘ (λ b → (a , b))) (η (lift tt))) Fa) ∎ }
