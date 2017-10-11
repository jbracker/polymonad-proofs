
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Bijection hiding ( refl ; sym ; trans )

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.Monoid renaming ( monoidMonoidalCategory to MonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor


module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.FromLaxMonoidalFunctor where 


LaxMonoidalFunctor→GradedLaxMonoidalFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                            → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                            → {CM : MonoidalCategory C} {DM : MonoidalCategory D}
                                            → LaxMonoidalFunctor (MonCat Mon ×CMon CM) DM
                                            → GradedLaxMonoidalFunctor Mon CM DM 
LaxMonoidalFunctor→GradedLaxMonoidalFunctor {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓMon} {M} Mon {C} {D} {CM} {DM} LMF = 
  gradedLaxMonoidalFunctor F ε μ-nat assoc' left-unitality' right-unitality'
  where
    open Category renaming ( id to cat-id ) hiding ( assoc )
    open MonoidalCategory hiding ( Obj ; Hom ; id ; _∘_ ; assoc )
    open Monoid Mon renaming ( ε to mon-ε ; assoc to mon-assoc ; left-id to mon-left-id ; right-id to mon-right-id )
    open LaxMonoidalFunctor LMF renaming ( F to laxF ; F₀ to laxF₀ ; F₁ to laxF₁ )
    open NaturalTransformation renaming ( η to nat-η )
    
    _∘D_ = _∘_ D
    _⊗C₀_ = _⊗₀_ CM
    _⊗D₀_ = _⊗₀_ DM
    _⊗D₁_ = _⊗₁_ DM
    
    F₀ : M → Obj C → Obj D
    F₀ m c = [ laxF ]₀ (m , c)
    
    F₁ : (m : M) → {a b : Obj C} → Hom C a b → Hom D (F₀ m a) (F₀ m b)
    F₁ m {a} {b} f = [ laxF ]₁ (refl , f)
    
    F : M → Functor C D
    F m = functor (F₀ m) (F₁ m) (Functor.id laxF) (Functor.compose laxF)
    
    μ-nat : (i j : M) → NaturalTransformation [ tensor DM ]∘[ [ F i ]×[ F j ] ] [ F ((Mon Monoid.∙ i) j) ]∘[ tensor CM ]
    μ-nat i j = naturalTransformation (λ (x : Obj (C ×C C)) → μ (i , proj₁ x) (j , proj₂ x)) (natural μ-natural-transformation)
    
    abstract
      laxF-helper1 : {a b : Obj C} {m m' : M} → (f : Hom C a b) → (p : m ≡ m') → F₁ m' f ≅ laxF₁ (sym p , f)
      laxF-helper1 {a} {b} {m} {.m} f refl = hrefl
      
    abstract
      laxF-helper2 : {a b : Obj C} {m m' : M} → (f : Hom C a b) → (p : m ≡ m') → laxF₁ (p , f) ≅ F₁ m f
      laxF-helper2 {a} {b} {m} {.m} f refl = hrefl
    
    abstract
      assoc' : {i j k : M} (x y z : Obj C)
             → F₁ ((i ∙ j) ∙ k) (α CM x y z) ∘D (μ (i ∙ j , x ⊗C₀ y) (k , z) ∘D (μ (i , x) (j , y) ⊗D₁ (cat-id D)))
             ≅ μ (i , x) (j ∙ k , y ⊗C₀ z) ∘D ((cat-id D ⊗D₁ μ (j , y) (k , z)) ∘D (α DM (F₀ i x) (F₀ j y) (F₀ k z)))
      assoc' {i} {j} {k} x y z = begin 
        (Hom D ([ tensor DM ]₀ (F₀ i x , F₀ j y) ⊗D₀ F₀ k z) (F₀ ((i ∙ j) ∙ k) (x ⊗C₀ (y ⊗C₀ z))) ∋ F₁ ((i ∙ j) ∙ k) (α CM x y z) ∘D (μ (i ∙ j , x ⊗C₀ y) (k , z) ∘D (μ (i , x) (j , y) ⊗D₁ (cat-id D))))
          ≅⟨ hcong₂ (λ X Y → (Hom D ([ tensor DM ]₀ (F₀ i x , F₀ j y) ⊗D₀ F₀ k z) (F₀ X (x ⊗C₀ (y ⊗C₀ z))) ∋ Y ∘D (μ (i ∙ j , x ⊗C₀ y) (k , z) ∘D (μ (i , x) (j , y) ⊗D₁ (cat-id D))))) 
                    (≡-to-≅ (sym mon-assoc)) (laxF-helper1 (α CM x y z) mon-assoc) ⟩
        laxF₁ (sym (mon-assoc {i} {j} {k}) , α CM x y z) ∘D (μ ((i ∙ j) , (x ⊗C₀ y)) (k , z) ∘D (μ (i , x) (j , y) ⊗D₁ (cat-id D)))
          ≅⟨ ≡-to-≅ $ assoc (i , x) (j , y) (k , z) ⟩
        μ (i , x) (j ∙ k , y ⊗C₀ z) ∘D ((cat-id D ⊗D₁ μ (j , y) (k , z)) ∘D (α DM (F₀ i x) (F₀ j y) (F₀ k z))) ∎
    
    abstract
      left-unitality' : {i : M} (x : MonoidalCategory.Obj CM)
                      → λ' DM (Functor.F₀ (F i) x) 
                      ≅ F₁ (mon-ε ∙ i) (λ' CM x) ∘D (μ (mon-ε , unit CM) (i , x) ∘D (ε ⊗D₁ cat-id D))
      left-unitality' {i} x = begin
        λ' DM (Functor.F₀ (F i) x) 
          ≅⟨ ≡-to-≅ $ left-unitality (i , x) ⟩
        (Hom D ([ tensor DM ]₀ (unit DM , laxF₀ (i , x))) (laxF₀ (i , x)) ∋ laxF₁ (mon-left-id , λ' CM x) ∘D (μ (unit (MonCat Mon ×CMon CM)) (i , x) ∘D (ε ⊗D₁ cat-id D)))
          ≅⟨ hcong₂ (λ X Y → Hom D ([ tensor DM ]₀ (unit DM , laxF₀ (i , x))) (laxF₀ (X , x)) ∋ Y ∘D (μ (unit (MonCat Mon ×CMon CM)) (i , x) ∘D (ε ⊗D₁ cat-id D))) 
                    (≡-to-≅ (sym mon-left-id)) (laxF-helper2 (λ' CM x) mon-left-id) ⟩
        F₁ (mon-ε ∙ i) (λ' CM x) ∘D (μ (mon-ε , unit CM) (i , x) ∘D (ε ⊗D₁ cat-id D)) ∎
    
    abstract
      right-unitality' : {i : M} (x : MonoidalCategory.Obj CM) 
                       → ρ DM (Functor.F₀ (F i) x) 
                       ≅ F₁ (i ∙ mon-ε) (ρ CM x) ∘D (μ (i , x) (mon-ε , unit CM) ∘D (cat-id D ⊗D₁ ε))
      right-unitality' {i} c = begin
        ρ DM (Functor.F₀ (F i) c) 
          ≅⟨ ≡-to-≅ $ right-unitality (i , c) ⟩ 
        (Hom D ([ tensor DM ]₀ (laxF₀ (i , c) , unit DM)) (laxF₀ (i , c)) ∋ laxF₁ (mon-right-id , ρ CM c) ∘D (μ (i , c) (unit (MonCat Mon ×CMon CM)) ∘D  (cat-id D ⊗D₁ ε)))
          ≅⟨ hcong₂ (λ X Y → Hom D ([ tensor DM ]₀ (laxF₀ (i , c) , unit DM)) (laxF₀ (X , c)) ∋ Y ∘D (μ (i , c) (unit (MonCat Mon ×CMon CM)) ∘D  (cat-id D ⊗D₁ ε))) 
                    (≡-to-≅ (sym mon-right-id)) (laxF-helper2 (ρ CM c) mon-right-id) ⟩
        F₁ (i ∙ mon-ε) (ρ CM c) ∘D (μ (i , c) (mon-ε , unit CM) ∘D (cat-id D ⊗D₁ ε)) ∎
