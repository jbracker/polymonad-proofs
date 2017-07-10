 
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( sym to hsym ; trans to htrans ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Extensionality

open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Graded.Applicative
open import Haskell.Functor renaming ( Functor to HaskellFunctor )

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Examples.Discrete
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.SetCat
open import Theory.Category.Monoidal.Examples.Monoid
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation

module Theory.Functor.Monoidal.Properties.FromGradedApplicative where


GradedApplicative→MonoidalFunctor : {ℓ : Level} {M : Set ℓ} {mon : Monoid M} {F : M → TyCon}
                                  → GradedApplicative mon F → LaxMonoidalFunctor (monoidMonoidalCategory mon ×CMon setMonoidalCategory {zero}) (setMonoidalCategory {zero})
GradedApplicative→MonoidalFunctor {ℓ} {M} {mon} {F} applic = laxMonoidalFunctor fun ε' μ' assoc' left-id' right-id'
  where
    open Category
    open Functor
    open MonoidalCategory renaming ( α to ass )
    open NaturalTransformation hiding ( natural ) renaming ( η to nat-η )

    open Monoid mon
    
    MonMonCat = monoidMonoidalCategory mon
    MonCat = discreteCategory M
    
    SetMonCat = setMonoidalCategory {zero}
    SetCat = setCategory {zero}
    
    fun : Functor (MonCat ×C SetCat) SetCat
    fun = functor fun₀ fun₁ fun-id fun-compose
      where
        fun₀ : Obj (MonCat ×C SetCat) → Obj SetCat
        fun₀ (i , α) = F i α

        fun₁ : {a b : Obj (MonCat ×C SetCat)} → Hom (MonCat ×C SetCat) a b → Hom SetCat (fun₀ a) (fun₀ b)
        fun₁ {i , α} {.i , β} (refl , f) a = GradedApplicative.fmap applic {i} {α} {β} f a
        
        abstract
          fun-id : {a : Obj (MonCat ×C SetCat)} → (λ x → GradedApplicative.fmap applic {proj₁ a} {proj₂ a} (id SetCat) x) ≡ id SetCat
          fun-id {i , α} = HaskellFunctor.law-id (GradedApplicative.functor applic i)

        abstract
          fun-compose : {a b c : Obj (MonCat ×C SetCat)} {f : Hom (MonCat ×C SetCat) a b} {g : Hom (MonCat ×C SetCat) b c}
                      → fun₁ (_∘_ (MonCat ×C SetCat) g f) ≡ fun₁ g ∘F fun₁ f
          fun-compose {i , α} {.i , β} {.i , γ} {refl , f} {refl , g} = HaskellFunctor.law-compose (GradedApplicative.functor applic i) g f

    abstract
      fun-cong : {i j : M} {α β : Type}
               → (f : α → β) (x : F j α)
               → (p : j ≡ i)
               → ((F i β) ∋ (F₁ fun (p , f)) x)
               ≅ ((F j β) ∋ (F₁ fun (refl , f)) x)
      fun-cong {i} {.i} {α} {β} f x refl = refl
    
    ε' : MonoidalCategory.Hom SetMonCat (unit SetMonCat) (F₀ fun (unit (MonMonCat ×CMon SetMonCat)))
    ε' (lift tt) = GradedApplicative.unit applic
    
    μ' : NaturalTransformation [ tensor SetMonCat ]∘[ [ fun ]×[ fun ] ] [ fun ]∘[ tensor (MonMonCat ×CMon SetMonCat) ]
    μ' = naturalTransformation nat-μ natural
      where
        nat-μ : (x : Obj ((MonCat ×C SetCat) ×C (MonCat ×C SetCat)))
              → Hom SetCat ([ [ tensor SetMonCat ]∘[ [ fun ]×[ fun ] ] ]₀ x) ([ [ fun ]∘[ tensor (MonMonCat ×CMon SetMonCat) ] ]₀ x)
        nat-μ ((i , α) , (j , β)) (Fiα , Fjβ) = GradedApplicative._**_ applic {i} {j} {α} {β} Fiα Fjβ

        abstract
          natural : {a b : Obj ((MonCat ×C SetCat) ×C (MonCat ×C SetCat))}
                  → {f : Hom ((MonCat ×C SetCat) ×C (MonCat ×C SetCat)) a b}
                  → [ [ fun ]∘[ tensor (MonMonCat ×CMon SetMonCat) ] ]₁ f ∘F nat-μ a
                  ≡ nat-μ b ∘F [ [ tensor SetMonCat ]∘[ [ fun ]×[ fun ] ] ]₁ f
          natural {(i , α₀) , (j , α₁)} {(.i , β₀) , (.j , β₁)} {(refl , f) , (refl , g)}
            = fun-ext (λ {(Fiα₀ , Fjα₁) → GradedApplicative.law-naturality applic f g Fiα₀ Fjα₁})

    open GradedApplicative applic

    abstract
      assoc' : (x y z : MonoidalCategory.Obj (MonMonCat ×CMon SetMonCat))
             → F₁ fun (ass (MonMonCat ×CMon SetMonCat) x y z) ∘F (nat-η μ' (((MonMonCat ×CMon SetMonCat) ⊗₀ x) y , z) ∘F ((SetMonCat ⊗₁ nat-η μ' (x , y)) (λ x → x)))
             ≡ nat-η μ' (x , ((MonMonCat ×CMon SetMonCat) ⊗₀ y) z) ∘F ((SetMonCat ⊗₁ (λ x → x)) (nat-η μ' (y , z)) ∘F (ass SetMonCat (F₀ fun x) (F₀ fun y) (F₀ fun z)))
      assoc' (i , α) (j , β) (k , γ) = fun-ext (λ { ((Fiα , Fjβ) , Fkγ) → ≅-to-≡ $ begin
        (F (i ∙ (j ∙ k)) (α × (β × γ)) ∋ (F₁ fun (ass MonMonCat i j k , ass SetMonCat α β γ)) ((Fiα ** Fjβ) ** Fkγ))
          ≅⟨ fun-cong (ass SetMonCat α β γ) ((Fiα ** Fjβ) ** Fkγ) (ass MonMonCat i j k) ⟩
        (F ((i ∙ j) ∙ k) (α × (β × γ)) ∋ fmap {i = (i ∙ j) ∙ k} (λ {((a , b) , c) → (a , (b , c))}) ( (Fiα ** Fjβ) ** Fkγ ) )
          ≅⟨ hsym (law-associativity Fiα Fjβ Fkγ) ⟩
        (Fiα ** (Fjβ ** Fkγ)) ∎ })

    abstract
      left-id' : (x : MonoidalCategory.Obj (MonMonCat ×CMon SetMonCat))
               → λ' SetMonCat (F₀ fun x)
               ≡ F₁ fun (λ' (MonMonCat ×CMon SetMonCat) x) ∘F (nat-η μ' ((ε , Lift ⊤) , x) ∘F ((SetMonCat ⊗₁ ε') (λ x → x)))
      left-id' (i , α) = fun-ext (λ { (lift tt , Fiα) → ≅-to-≡ $ begin
        Fiα
          ≅⟨ hsym (law-left-identity' Fiα) ⟩
        fmap proj₂ (GradedApplicative.unit applic ** Fiα)
          ≅⟨ hsym (fun-cong proj₂ (GradedApplicative.unit applic ** Fiα) (Monoid.left-id mon)) ⟩
        (F₁ fun (λ' (MonMonCat ×CMon SetMonCat) (i , α))) (GradedApplicative.unit applic ** Fiα) ∎})

    abstract
      right-id' : (x : MonoidalCategory.Obj (MonMonCat ×CMon SetMonCat))
                → ρ SetMonCat (F₀ fun x)
                ≡ (F₁ fun (ρ (MonMonCat ×CMon setMonoidalCategory) x)) ∘F ((nat-η μ' (x , MonoidalCategory.unit (MonMonCat ×CMon SetMonCat))) ∘F ((SetMonCat ⊗₁ (λ x → x)) ε'))
      right-id' (i , α) = fun-ext (λ {(Fiα , lift tt)
                        → ≅-to-≡ (htrans (hsym (law-right-identity' Fiα))
                                         (hsym (fun-cong proj₁ (Fiα ** GradedApplicative.unit applic) (Monoid.right-id mon))))})
