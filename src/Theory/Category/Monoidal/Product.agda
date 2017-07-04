
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Extensionality
open import Equality

open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition
open import Theory.Category.Monoidal
open import Theory.Category.Isomorphism
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Functor.Application
open import Theory.Functor.Association
open import Theory.Natural.Transformation
open import Theory.Natural.Isomorphism

module Theory.Category.Monoidal.Product where

productMonoidalCategory : {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} 
                        → {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} 
                        → MonoidalCategory C → MonoidalCategory D → MonoidalCategory (C ×C D)
productMonoidalCategory {ℓC₀} {ℓC₁} {ℓD₀} {ℓD₁} {C} {D} CMon DMon 
  = monoidalCategory tensor' unit' associator' lunitor' runitor' 
                     (λ x y → Σ-eq (triangle-id CMon (proj₁ x) (proj₁ y)) (≡-to-≅ $ triangle-id DMon (proj₂ x) (proj₂ y)))
                     (λ w x y z → Σ-eq (pentagon-id CMon (proj₁ w) (proj₁ x) (proj₁ y) (proj₁ z)) (≡-to-≅ $ pentagon-id DMon (proj₂ w) (proj₂ x) (proj₂ y) (proj₂ z)))
  where
    open Category
    open MonoidalCategory
    open NaturalIsomorphism renaming ( η to iso-η )

    _∘C×D_ = λ {a b c} → _∘_ (C ×C D) {a} {b} {c}
    
    switch : Functor ((C ×C D) ×C (C ×C D)) ((C ×C C) ×C (D ×C D))
    switch = functor (λ {((c₀ , d₀) , (c₁ , d₁)) → (c₀ , c₁) , (d₀ , d₁)}) 
                     (λ {((f₀ , g₀) , (f₁ , g₁)) → (f₀ , f₁) , (g₀ , g₁)}) 
                     refl refl
    
    tensor' : Functor ((C ×C D) ×C (C ×C D)) (C ×C D)
    tensor' = [ [ tensor CMon ]×[ tensor DMon ] ]∘[ switch ]
    
    unit' : Obj (C ×C D)
    unit' = unit CMon , unit DMon
    
    open Theory.Functor.Association.Associator
    open Theory.Functor.Application.BiFunctor
    
    t2C : Obj ((C ×C D) ×C (C ×C D) ×C (C ×C D)) → Obj (C ×C C ×C C)
    t2C ((c₀ , d₀) ,' (c₁ , d₁) ,' (c₂ , d₂)) = c₀ ,' c₁ ,' c₂
    
    t2D : Obj ((C ×C D) ×C (C ×C D) ×C (C ×C D)) → Obj (D ×C D ×C D)
    t2D ((c₀ , d₀) ,' (c₁ , d₁) ,' (c₂ , d₂)) = d₀ ,' d₁ ,' d₂
    
    associator' : NaturalIsomorphism (leftAssociator tensor') (Associator.rightAssociator tensor')
    associator' = naturalIsomorphism (naturalTransformation η nat) iso
      where
        η : (x : Obj ((C ×C D) ×C (C ×C D) ×C (C ×C D))) → Hom (C ×C D) ([ leftAssociator tensor' ]₀ x) ([ rightAssociator tensor' ]₀ x)
        η x = iso-η (associator CMon) (t2C x) , iso-η (associator DMon) (t2D x)
        
        abstract
          nat : {a b : Obj ((C ×C D) ×C C ×C D ×C (C ×C D))} {f : Hom ((C ×C D) ×C C ×C D ×C (C ×C D)) a b}
              → ((C ×C D) ∘ [ rightAssociator tensor' ]₁ f) (η a) ≡ ((C ×C D) ∘ η b) ([ leftAssociator tensor' ]₁ f)
          nat = (Σ-eq (η-natural (associator CMon)) (≡-to-≅ (η-natural (associator DMon))))
        
        iso : (x : Obj ((C ×C D) ×C (C ×C D) ×C (C ×C D))) → Isomorphism (C ×C D) (η x)
        iso x = isomorphism (inv (associator CMon) (t2C x) , inv (associator DMon) (t2D x)) 
                            (Σ-eq (inv-left-id  (associator CMon) (t2C x)) (≡-to-≅ $ inv-left-id  (associator DMon) (t2D x)))
                            (Σ-eq (inv-right-id (associator CMon) (t2C x)) (≡-to-≅ $ inv-right-id (associator DMon) (t2D x)))
        
    lunitor' : NaturalIsomorphism ([ unit' ,-] tensor') Id[ C ×C D ]
    lunitor' = naturalIsomorphism (naturalTransformation (λ x → (iso-η (left-unitor CMon) (proj₁ x)) , (iso-η (left-unitor DMon) (proj₂ x))) 
                                                         (Σ-eq (η-natural (left-unitor CMon)) (≡-to-≅ $ η-natural (left-unitor DMon)))) 
             $ λ x → isomorphism (inv (left-unitor CMon) (proj₁ x) , inv (left-unitor DMon) (proj₂ x)) 
                                 (Σ-eq (inv-left-id  (left-unitor CMon) (proj₁ x)) (≡-to-≅ $ inv-left-id  (left-unitor DMon) (proj₂ x)))
                                 (Σ-eq (inv-right-id (left-unitor CMon) (proj₁ x)) (≡-to-≅ $ inv-right-id (left-unitor DMon) (proj₂ x)))
    
    runitor' : NaturalIsomorphism ([-, unit' ] tensor') Id[ C ×C D ]
    runitor' = naturalIsomorphism (naturalTransformation (λ x → iso-η (right-unitor CMon) (proj₁ x) , iso-η (right-unitor DMon) (proj₂ x)) 
                                                         (Σ-eq (η-natural (right-unitor CMon)) (≡-to-≅ $ η-natural (right-unitor DMon)))) 
             $ λ x → isomorphism (inv (right-unitor CMon) (proj₁ x) , inv (right-unitor DMon) (proj₂ x))
                                 (Σ-eq (inv-left-id  (right-unitor CMon) (proj₁ x)) (≡-to-≅ $ inv-left-id  (right-unitor DMon) (proj₂ x)))
                                 (Σ-eq (inv-right-id (right-unitor CMon) (proj₁ x)) (≡-to-≅ $ inv-right-id (right-unitor DMon) (proj₂ x)))
    
_×CMon_ = productMonoidalCategory
