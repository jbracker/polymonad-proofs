
-- Stdlib
open import Level
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; cong to hcong ; cong₂ to hcong₂ )
open ≅-Reasoning 

-- Local
open import Congruence

open import Theory.Category.Definition
open import Theory.Functor.Definition
open import Theory.Natural.Transformation

module Theory.Haskell.Parameterized.Relative.Monad where

open Category hiding ( right-id ; left-id )

-- -----------------------------------------------------------------------------
-- Definition of a parameterized relative monad
-- -----------------------------------------------------------------------------
record ParameterizedRelativeMonad {ℓC₀ ℓC₁ ℓD₀ ℓD₁ ℓI₀ ℓI₁ : Level} 
                                  {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (I : Category {ℓI₀} {ℓI₁}) 
                                  (T : {i j : Obj I} → Hom I i j → Obj C → Obj D) 
                                  (J : Functor C D) : Set (ℓC₀ ⊔ ℓC₁ ⊔ ℓD₀ ⊔ ℓD₁ ⊔ ℓI₀ ⊔ ℓI₁) where
  constructor parameterizedRelativeMonad
  
  private
    _∘D_ = _∘_ D
    _∘C_ = _∘_ C
    _∘I_ = _∘_ I
  
  field
    η :  (i : Obj I) → {a : Obj C} → Hom D ([ J ]₀ a) (T (id I {i}) a)
    
    kext : {i j k : Obj I} → (f : Hom I i j) (g : Hom I j k) 
         → {a b : Obj C} → Hom D ([ J ]₀ a) (T f b) → Hom D (T g a) (T (g ∘I f) b)
    
    right-id : {i j : Obj I} → (f : Hom I i j) 
             → {a b : Obj C} {k : Hom D ([ J ]₀ a) (T f b)} 
             → kext f (id I) k ∘D η j ≅ k
    
    left-id : {i j : Obj I} → (f : Hom I i j) 
            → {a : Obj C}
            → kext (id I) f (η i {a}) ≅ id D {a = T f a}
    
    coher : {i j v w : Obj I} → (f : Hom I i j) → (g : Hom I j v) → (h : Hom I v w) 
          → {a b c : Obj C} {k : Hom D ([ J ]₀ a) (T g b)} {l : Hom D ([ J ]₀ b) (T f c)} 
          → kext (g ∘I f) h ( (kext f g l) ∘D k ) ≅ kext f (h ∘I g) l ∘D kext g h k
  
  abstract
    functor-kext-compose : {i j : Obj I} → (fI : Hom I i j) 
                         → {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} 
                         → kext (id I) fI (η i ∘D [ J ]₁ (g ∘C f)) ≅ kext (id I) (fI ∘I id I) (η i ∘D [ J ]₁ g) ∘D (kext (id I) fI (η i ∘D [ J ]₁ f))
    functor-kext-compose {i} {j} fI {a} {b} {c} {f} {g} = begin
      kext (id I) fI (η i ∘D [ J ]₁ (g ∘C f)) 
        ≡⟨ cong (λ X → kext (id I) fI (η i ∘D X)) (Functor.compose J) ⟩
      kext (id I) fI (η i ∘D ([ J ]₁ g ∘D [ J ]₁ f))
        ≡⟨ cong (kext (id I) fI) (assoc D) ⟩
      kext (id I) fI ((η i ∘D [ J ]₁ g) ∘D [ J ]₁ f)
        ≅⟨ hcong₂ (λ X Y → kext X fI (Y ∘D [ J ]₁ f)) (≡-to-≅ (sym (Category.right-id I))) (hsym $ right-id (id I)) ⟩
      kext (id I ∘I id I) fI ((kext (id I) (id I) (η i ∘D [ J ]₁ g) ∘D η i) ∘D [ J ]₁ f)
        ≡⟨ cong (kext (id I ∘I id I) fI) (sym (assoc D)) ⟩
      kext (id I ∘I id I) fI (kext (id I) (id I) (η i ∘D [ J ]₁ g) ∘D (η i ∘D [ J ]₁ f))
        ≅⟨ coher (id I) (id I) fI ⟩
      kext (id I) (fI ∘I id I) (η i ∘D [ J ]₁ g) ∘D (kext (id I) fI (η i ∘D [ J ]₁ f)) ∎
  
  FunctorT : {i j : Obj I} → (f : Hom I i j) → Functor C D
  FunctorT {i} {j} f = functor T₀ T₁ T-id T-compose
    where
      T₀ = T f
      
      T₁ : {a b : Obj C} → Hom C a b → Hom D (T f a) (T f b)
      T₁ {a} {b} k = subst (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ k))
      
      abstract
        T-id : {a : Obj C} → T₁ (id C {a}) ≡ id D
        T-id {a} = ≅-to-≡ $ begin
          T₁ (id C) 
            ≡⟨⟩ 
          subst (λ X → Hom D (T f a) (T X a)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ (id C)))
            ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X a)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ (id C))) ⟩ 
          kext (id I) f (η i ∘D [ J ]₁ (id C))
            ≡⟨ cong (λ X → kext (id I) f (η i ∘D X)) (Functor.id J) ⟩ 
          kext (id I) f (η i ∘D id D)
            ≡⟨ cong (kext (id I) f) (Category.left-id D) ⟩ 
          kext (id I) f (η i)
            ≅⟨ left-id f ⟩
          id D ∎
      
      abstract
        T-compose : {a b c : Obj C} {g : Hom C a b} {h : Hom C b c} 
                  → T₁ (h ∘C g) ≡ T₁ h ∘D T₁ g
        T-compose {a} {b} {c} {g} {h} = ≅-to-≡ $ begin
          T₁ (h ∘C g)
            ≡⟨⟩
          subst (λ X → Hom D (T f a) (T X c)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ (h ∘C g)))
            ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X c)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ (h ∘C g))) ⟩
          kext (id I) f (η i ∘D [ J ]₁ (h ∘C g))
            ≅⟨ functor-kext-compose f ⟩
          kext (id I) (f ∘I id I) (η i ∘D [ J ]₁ h) ∘D kext (id I) f (η i ∘D [ J ]₁ g)
            ≅⟨ hcong₂ (λ Y Z → kext (id I) Y (η i ∘D [ J ]₁ h) ∘D Z) 
                      (≡-to-≅ (Category.left-id I)) 
                      (hsym (≡-subst-removable (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ g)))) ⟩
          kext (id I) f (η i ∘D [ J ]₁ h) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ g))
            ≅⟨ hcong₂ (λ Y Z → (Hom D (T f b) (T Y c) ∋ Z) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ g))) 
                      (≡-to-≅ (Category.left-id I)) 
                      (hsym (≡-subst-removable (λ X → Hom D (T f b) (T X c)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ h)))) ⟩
          subst (λ X → Hom D (T f b) (T X c)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ h)) ∘D subst (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ g))
            ≡⟨⟩
          T₁ h ∘D T₁ g ∎
  
  abstract
    functor-kext-coher : {i j : Obj I} → (fI : Hom I i j)
                       → {a b : Obj C} → (f : Hom C a b)
                       → [ FunctorT fI ]₁ f ≅ kext (id I) fI (η i ∘D [ J ]₁ f)
    functor-kext-coher {i} {j} f {a} {b} k = begin
      [ FunctorT f ]₁ k 
        ≡⟨⟩
      subst (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ k))
        ≅⟨ ≡-subst-removable (λ X → Hom D (T f a) (T X b)) (Category.left-id I) (kext (id I) f (η i ∘D [ J ]₁ k)) ⟩
      kext (id I) f (η i ∘D [ J ]₁ k) ∎
  
  NaturalTransformation-η : (i : Obj I)
                          → NaturalTransformation J (FunctorT (id I {i}))
  NaturalTransformation-η i = naturalTransformation (λ x → η i {x}) natural
    where
      abstract
        natural : {a b : Obj C} {f : Hom C a b} 
                → [ FunctorT (id I) ]₁ f ∘D (η i) ≡ η i ∘D [ J ]₁ f
        natural {a} {b} {f} = ≅-to-≡ $ begin
          [ FunctorT (id I) ]₁ f ∘D η i
            ≡⟨⟩
          subst (λ X → Hom D (T (id I {i}) a) (T X b)) (Category.left-id I {i}) (kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f)) ∘D η i 
            ≅⟨ hcong₂ (λ X Y → (Hom D (T (id I {i}) a) (T X b) ∋ Y) ∘D η i) 
                      (≡-to-≅ (sym (Category.left-id I {i}))) 
                      (≡-subst-removable (λ X → Hom D (T (id I {i}) a) (T X b)) (Category.left-id I {i}) (kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f))) ⟩
          kext (id I {i}) (id I {i}) (η i ∘D [ J ]₁ f) ∘D η i 
            ≅⟨ right-id (id I {i}) ⟩
          η i ∘D [ J ]₁ f ∎
  
  NaturalTransformation-kext : {i j : Obj I} → (fI : Hom I i j)
                             → NaturalTransformation (FunctorT fI) (FunctorT fI)
  NaturalTransformation-kext {i} {j} fI = naturalTransformation nat-η natural
    where 
      nat-η : (x : Obj C) → Hom D ([ FunctorT fI ]₀ x) ([ FunctorT fI ]₀ x)
      nat-η x = subst (λ X → Hom D (T fI x) (T X x)) (Category.left-id I) (kext (id I) fI (η i {x}))

      abstract
        natural : {a b : Obj C} {f : Hom C a b} 
                → [ FunctorT fI ]₁ f ∘D nat-η a ≡ nat-η b ∘D [ FunctorT fI ]₁ f
        natural {a} {b} {f} = ≅-to-≡ $ begin
           [ FunctorT fI ]₁ f ∘D nat-η a 
             ≡⟨⟩
           subst (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f)) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.left-id I) (kext (id I) fI (η i {a}))
             ≅⟨ hcong₂ (λ Y Z → (Hom D (T fI a) (T Y b) ∋ Z) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.left-id I) (kext (id I) fI (η i {a}))) 
                       (≡-to-≅ (sym (Category.left-id I))) 
                       (≡-subst-removable (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f))) ⟩
           kext (id I) fI (η i ∘D [ J ]₁ f) ∘D subst (λ X → Hom D (T fI a) (T X a)) (Category.left-id I) (kext (id I) fI (η i {a}))
             ≅⟨ hcong₂ (λ Y Z → kext (id I) Y (η i ∘D [ J ]₁ f) ∘D Z) 
                       (≡-to-≅ (sym $ Category.left-id I))
                       (≡-subst-removable (λ X → Hom D (T fI a) (T X a)) (Category.left-id I) (kext (id I) fI (η i {a}))) ⟩
           kext (id I) (fI ∘I id I) (η i ∘D [ J ]₁ f) ∘D kext (id I) fI (η i {a})
             ≅⟨ hcong₂ (λ X Y → kext (id I) X (η i ∘D [ J ]₁ f) ∘D Y) 
                       (≡-to-≅ (Category.left-id I)) 
                       (left-id fI) ⟩
           kext (id I) fI (η i ∘D [ J ]₁ f) ∘D id D
             ≅⟨ hcong (λ X → kext (id I) X (η i ∘D [ J ]₁ f) ∘D id D) (≡-to-≅ (sym (Category.left-id I))) ⟩
           kext (id I) (fI ∘I id I) (η i ∘D [ J ]₁ f) ∘D id D
             ≡⟨ Category.left-id D ⟩
           kext (id I) (fI ∘I id I) (η i ∘D [ J ]₁ f)
             ≅⟨ hcong (λ X → kext (id I) X (η i ∘D [ J ]₁ f)) (≡-to-≅ (Category.left-id I)) ⟩
           kext (id I) fI (η i ∘D [ J ]₁ f)
             ≡⟨ sym (Category.right-id D) ⟩
           id D {T (fI ∘I id I) b} ∘D kext (id I) fI (η i ∘D [ J ]₁ f)
             ≅⟨ hcong₂ (λ X Y → (Hom D (T fI a) (T X b)) ∋ (Y ∘D kext (id I) fI (η i ∘D [ J ]₁ f))) (≡-to-≅ (sym (Category.left-id I))) (hsym (left-id (fI ∘I id I))) ⟩
           kext (id I) (fI ∘I id I) (η i {b}) ∘D kext (id I) fI (η i ∘D [ J ]₁ f)
             ≅⟨ hcong₂ (λ Y Z → kext (id I) Y (η i {b}) ∘D Z) 
                       (≡-to-≅ (Category.left-id I))
                       (hsym (≡-subst-removable (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f)))) ⟩
           kext (id I) fI (η i {b}) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f))
             ≅⟨ hcong₂ (λ Y Z → (Hom D (T fI b) (T Y b) ∋ Z) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f))) 
                       (≡-to-≅ (Category.left-id I)) 
                       (hsym (≡-subst-removable (λ X → Hom D (T fI b) (T X b)) (Category.left-id I) (kext (id I) fI (η i {b})))) ⟩
           subst (λ X → Hom D (T fI b) (T X b)) (Category.left-id I) (kext (id I) fI (η i {b})) ∘D subst (λ X → Hom D (T fI a) (T X b)) (Category.left-id I) (kext (id I) fI (η i ∘D [ J ]₁ f))
             ≡⟨⟩
           nat-η b ∘D [ FunctorT fI ]₁ f ∎
