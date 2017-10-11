
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning

open import Bijection hiding ( refl ; sym ; trans )

open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.Discrete renaming ( discreteCategory to Disc )
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Product
open import Theory.Category.Monoidal.Examples.Monoid renaming ( monoidMonoidalCategory to MonCat )
open import Theory.Functor.Definition
open import Theory.Functor.Monoidal
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor


module Theory.Haskell.Parameterized.Graded.LaxMonoidalFunctor.Properties.ToLaxMonoidalFunctor where 

GradedLaxMonoidalFunctor→LaxMonoidalFunctor : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓMon : Level} {M : Set ℓMon} (Mon : Monoid M)
                                            → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}}
                                            → {CM : MonoidalCategory C} {DM : MonoidalCategory D}
                                            → GradedLaxMonoidalFunctor Mon CM DM 
                                            → LaxMonoidalFunctor (MonCat Mon ×CMon CM) DM
GradedLaxMonoidalFunctor→LaxMonoidalFunctor {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {ℓMon} {M} Mon {C} {D} {CM} {DM} GLMF = 
  laxMonoidalFunctor F ε μ-nat assoc' left-unitality' right-unitality'
  where
    
    open Monoid Mon renaming ( assoc to mon-assoc ; left-id to mon-left-id ; right-id to mon-right-id ; ε to mon-ε )
    open Category renaming ( assoc to cat-assoc ; id to cat-id )
    open MonoidalCategory hiding ( Obj ; Hom ; _∘_ ) renaming ( assoc to moncat-assoc )
    open NaturalTransformation renaming ( η to nat-η )
    open GradedLaxMonoidalFunctor GLMF renaming ( F to gradF )

    gradF₀ : (m : M) → Obj C → Obj D
    gradF₀ m = Functor.F₀ (gradF m)
    
    _∘M×C_ = _∘_ (Disc M ×C C)
    _∘D_ = _∘_ D
    
    _⊗C₀_ = _⊗₀_ CM
    _⊗D₀_ = _⊗₀_ DM
    
    F₀ : Obj (Disc M ×C C) → Obj D
    F₀ (m , c) = [ gradF m ]₀ c
    
    F₁ : {a b : Obj (Disc M ×C C)} → Hom (Disc M ×C C) a b → Hom D (F₀ a) (F₀ b)
    F₁ {m , a} {.m , b} (refl , f) = [ gradF m ]₁ f

    F-id : {a : Obj (Disc M ×C C)} → [ gradF (proj₁ a) ]₁ (cat-id C {proj₂ a}) ≡ cat-id D
    F-id {m , c} = Functor.id (gradF m)
    
    F-compose : {a b c : Obj (Disc M ×C C)} {f : Hom (Disc M ×C C) a b} {g : Hom (Disc M ×C C) b c}
              → F₁ (g ∘M×C f) ≡ F₁ g ∘D F₁ f
    F-compose {m , a} {.m , b} {.m , c} {refl , f} {refl , g}  = Functor.compose (gradF m)
    
    F : Functor (Disc M ×C C) D
    F = functor F₀ F₁ F-id (λ {a b c} {f} {g} → F-compose {a} {b} {c} {f} {g})
    
    μ' : (x : Obj ((Disc M ×C C) ×C (Disc M ×C C))) → Hom D ([ [ tensor DM ]∘[ [ F ]×[ F ] ] ]₀ x) ([ [ F ]∘[ tensor (MonCat Mon ×CMon CM) ] ]₀ x)
    μ' ((m , a) , (m' , b)) = μ m m' a b
    
    natural-μ' : {a b : Obj ((Disc M ×C C) ×C (Disc M ×C C))} {f : Hom ((Disc M ×C C) ×C (Disc M ×C C)) a b}
               → [ [ F ]∘[ tensor (MonCat Mon ×CMon CM) ] ]₁ f ∘D μ' a ≡ μ' b ∘D [ [ tensor DM ]∘[ [ F ]×[ F ] ] ]₁ f
    natural-μ' {(m , a) , (n , a')} {(.m , b) , (.n , b')} {(refl , f) , (refl , g)} = natural (μ-natural-transformation m n)
    
    μ-nat : NaturalTransformation [ tensor DM ]∘[ [ F ]×[ F ] ] [ F ]∘[ tensor (MonCat Mon ×CMon CM) ]
    μ-nat = naturalTransformation μ' (λ {a b} {f} → natural-μ' {a} {b} {f})
    
    abstract
      gradF-helper1 : {a b : Obj C} {m m' : M} → (f : Hom C a b) → (p : m ≡ m') → F₁ (sym p , f) ≅ Functor.F₁ (gradF m') f
      gradF-helper1 {a} {b} {m} {.m} f refl = hrefl
      
    abstract
      gradF-helper2 : {a b : Obj C} {m m' : M} → (f : Hom C a b) → (p : m ≡ m') → Functor.F₁ (gradF m) f ≅ F₁ (p , f) 
      gradF-helper2 {a} {b} {m} {.m} f refl = hrefl
    
    abstract
      assoc' : (x y z : Obj (Disc M ×C C)) 
             → F₁ (α (MonCat Mon ×CMon CM) x y z) ∘D (nat-η μ-nat (((MonCat Mon ×CMon CM) ⊗₀ x) y , z) ∘D ((DM ⊗₁ nat-η μ-nat (x , y)) (cat-id D)))
             ≡ nat-η μ-nat (x , ((MonCat Mon ×CMon CM) ⊗₀ y) z) ∘D ((DM ⊗₁ id DM) (nat-η μ-nat (y , z)) ∘D (α DM (F₀ x) (F₀ y) (F₀ z)))
      assoc' (m , a) (m' , b) (m'' , c) = ≅-to-≡ $ begin
        F₁ (α (MonCat Mon ×CMon CM) (m , a) (m' , b) (m'' , c)) ∘D (nat-η μ-nat ((m ∙ m' , a ⊗C₀ b) , (m'' , c)) ∘D ((DM ⊗₁ nat-η μ-nat ((m , a) , (m' , b))) (cat-id D)))
          ≅⟨ hrefl ⟩
        (Hom D ([ [ tensor DM ]∘[ [ gradF m ]×[ gradF m' ] ] ]₀ (a , b) ⊗D₀ [ gradF m'' ]₀ c) ([ gradF (m ∙ (m' ∙ m'')) ]₀ (a ⊗C₀ (b ⊗C₀ c))) ∋ 
             F₁ (sym (mon-assoc {m} {m'} {m''}) , α CM a b c) ∘D (nat-η μ-nat ((m ∙ m' , a ⊗C₀ b) , (m'' , c)) ∘D ((DM ⊗₁ nat-η μ-nat ((m , a) , (m' , b))) (cat-id D))))
          ≅⟨ hcong₂ (λ X Y → (Hom D ([ [ tensor DM ]∘[ [ gradF m ]×[ gradF m' ] ] ]₀ (a , b) ⊗D₀ [ gradF m'' ]₀ c) ([ gradF X ]₀ (a ⊗C₀ (b ⊗C₀ c))) 
                                  ∋ Y ∘D (nat-η (μ-natural-transformation (m ∙ m') m'') ((CM ⊗₀ a) b , c) ∘D ((DM ⊗₁ nat-η (μ-natural-transformation m m') (a , b)) (id DM)))) ) 
                    (≡-to-≅ mon-assoc) (gradF-helper1 (α CM a b c) mon-assoc) ⟩
        (Hom D ([ [ tensor DM ]∘[ [ gradF m ]×[ gradF m' ] ] ]₀ (a , b) ⊗D₀ [ gradF m'' ]₀ c) ([ gradF ((m ∙ m') ∙ m'') ]₀ (a ⊗C₀ (b ⊗C₀ c))) ∋ 
             Functor.F₁ (gradF ((m ∙ m') ∙ m'')) (α CM a b c) ∘D (nat-η (μ-natural-transformation (m ∙ m') m'') (a ⊗C₀ b , c) ∘D ((DM ⊗₁ nat-η (μ-natural-transformation m m') (a , b)) (id DM))))
          ≅⟨ assoc {m} {m'} {m''} a b c ⟩
        nat-η (μ-natural-transformation m (m' ∙ m'')) (a , (CM ⊗₀ b) c) ∘D ((DM ⊗₁ id DM) (nat-η (μ-natural-transformation m' m'') (b , c)) ∘D (α DM (gradF₀ m a) (gradF₀ m' b) (gradF₀ m'' c)))
          ≅⟨ hrefl ⟩
        nat-η μ-nat ((m , a) , ((MonCat Mon ×CMon CM) ⊗₀ (m' , b)) (m'' , c)) ∘D ((DM ⊗₁ id DM) (nat-η μ-nat ((m' , b) , (m'' , c))) ∘D (α DM (F₀ (m , a)) (F₀ (m' , b)) (F₀ (m'' , c)))) ∎
    
    abstract
      left-unitality' : (x : MonoidalCategory.Obj (MonCat Mon ×CMon CM))
                      → λ' DM (Functor.F₀ F x)
                      ≡ Functor.F₁ F (λ' (MonCat Mon ×CMon CM) x) ∘D (nat-η μ-nat (unit (MonCat Mon ×CMon CM) , x) ∘D ((DM ⊗₁ ε) (id DM)))
      left-unitality' (m , a) = ≅-to-≡ $ begin
        λ' DM (Functor.F₀ F (m , a))
          ≅⟨ left-unitality {m} a ⟩
        (Hom D ([ tensor DM ]₀ (unit DM , [ gradF m ]₀ a)) ([ gradF (mon-ε ∙ m) ]₀ a) ∋ 
            Functor.F₁ (gradF (mon-ε ∙ m)) (λ' CM a) ∘D (nat-η (μ-natural-transformation mon-ε m) (unit CM , a) ∘D ((DM ⊗₁ ε) (id DM))))
          ≅⟨ (hcong₂ (λ X Y → (Hom D ([ tensor DM ]₀ (unit DM , [ gradF m ]₀ a)) ([ gradF X ]₀ a) ∋ Y ∘D (nat-η (μ-natural-transformation mon-ε m) (unit CM , a) ∘D ((DM ⊗₁ ε) (id DM))))) 
                     (≡-to-≅ mon-left-id) (gradF-helper2 (λ' CM a) mon-left-id)) ⟩
        (Hom D ([ tensor DM ]₀ (unit DM , [ gradF m ]₀ a)) ([ gradF m ]₀ a) ∋ 
            F₁ (λ' (MonCat Mon ×CMon CM) (m , a)) ∘D (nat-η μ-nat (unit (MonCat Mon ×CMon CM) , (m , a)) ∘D ((DM ⊗₁ ε) (id DM)))) ∎
    
    abstract
      right-unitality' : (x : MonoidalCategory.Obj (MonCat Mon ×CMon CM)) 
                       → ρ DM (Functor.F₀ F x)
                       ≡ Functor.F₁ F (ρ (MonCat Mon ×CMon CM) x) ∘D (nat-η μ-nat (x , unit (MonCat Mon ×CMon CM)) ∘D ((DM ⊗₁ id DM) ε))
      right-unitality' (m , a) = ≅-to-≡ $ begin
        ρ DM (Functor.F₀ F (m , a))
          ≅⟨ right-unitality {m} a ⟩
        (Hom D ([ tensor DM ]₀ ([ gradF m ]₀ a , unit DM)) ([ gradF (m ∙ mon-ε) ]₀ a) ∋ 
            Functor.F₁ (gradF (m ∙ mon-ε)) (ρ CM a) ∘D (nat-η (μ-natural-transformation m mon-ε) (a , unit CM) ∘D ((DM ⊗₁ id DM) ε)))
          ≅⟨ (hcong₂ (λ X Y → (Hom D ([ tensor DM ]₀ ([ gradF m ]₀ a , unit DM)) ([ gradF X ]₀ a) ∋ Y ∘D (nat-η (μ-natural-transformation m mon-ε) (a , unit CM) ∘D ((DM ⊗₁ id DM) ε)))) 
                     (≡-to-≅ mon-right-id) (gradF-helper2 (ρ CM a) mon-right-id)) ⟩
        (Hom D ([ tensor DM ]₀ ([ gradF m ]₀ a , unit DM)) ([ gradF m ]₀ a) ∋ 
            F₁ (ρ (MonCat Mon ×CMon CM) (m , a)) ∘D (nat-η μ-nat ((m , a) , unit (MonCat Mon ×CMon CM)) ∘D ((DM ⊗₁ id DM) ε))) ∎
