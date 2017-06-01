
open import Level
open import Function renaming ( _∘_ to _∘F_ ) hiding ( id )

open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Utilities
open import Extensionality
open import Theory.Category.Definition
open import Theory.Category.Examples
open import Theory.Functor.Definition
open import Theory.Functor.Constant
open import Theory.Functor.Application
open import Theory.End.Wedge
open import Theory.End.Definition
open import Theory.Natural.Transformation
open import Theory.Natural.ExtranaturalTransformation

open Category

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

module Theory.End.Examples where
  
  private
    module NatTransEnd {ℓC₀ ℓC₁ ℓD₀ ℓD₁ : Level} {C : Category {ℓC₀} {ℓC₁}} {D : Category {ℓD₀} {ℓD₁}} (F G : Functor C D) where
      private
        _∘C_ = _∘_ C
      _∘Cop_ = _∘_ (C op)
      _∘D_ = _∘_ D
      Set' = setCategory
      C×C = C op ×C C
      _∘C×C_ = _∘_ C×C
  
      open Functor F renaming ( id to F-id ; compose to F-compose )
      open Functor G renaming ( id to G-id ; compose to G-compose ; F₀ to G₀ ; F₁ to G₁ )
  
      W : Functor C×C (Set' {ℓD₁})
      W = functor W₀ W₁ W-id W-compose
        where
          W₀ : Obj C×C → Obj (Set' {ℓD₁})
          W₀ (c ,' c') = Hom D (F₀ c) (G₀ c')
      
          W₁ : {a b : Obj C×C} → Hom C×C a b → Hom (Set' {ℓD₁}) (W₀ a) (W₀ b)
          W₁ {a} {b} (f ,' g) h = G₁ g ∘D (h ∘D F₁ f)
          
          W-id : {a : Obj C×C} → W₁ (id C×C {a}) ≡ id (Set' {ℓD₁})
          W-id {c ,' c'} = fun-ext (λ f → trans (cong (λ Y → Y ∘D (f ∘D F₁ (id (C op) {c}))) (G-id)) (trans (right-id D) (trans (cong (λ Y → f ∘D Y) (F-id)) (left-id D))))
    
          W-compose : {a b c : Obj C×C} {f : Hom C×C a b} {g : Hom C×C b c} 
                    → W₁ (g ∘C×C f) ≡ W₁ g ∘F W₁ f
          W-compose {a} {b} {c} {f ,' f'} {g ,' g'} = fun-ext $ λ h → begin
            W₁ (g ∘Cop f ,' g' ∘C f') h
              ≡⟨⟩
            G₁ (g' ∘C f') ∘D (h ∘D F₁ (g ∘Cop f))
              ≡⟨ cong₂ (λ X Y → X ∘D (h ∘D Y)) G-compose F-compose ⟩
            (G₁ g' ∘D G₁ f') ∘D (h ∘D (F₁ f ∘D F₁ g))
              ≡⟨ sym $ assoc D ⟩
            G₁ g' ∘D (G₁ f' ∘D (h ∘D (F₁ f ∘D F₁ g)))
              ≡⟨ cong (λ X → G₁ g' ∘D (G₁ f' ∘D X)) (assoc D) ⟩
            G₁ g' ∘D (G₁ f' ∘D ((h ∘D F₁ f) ∘D F₁ g)) 
              ≡⟨ cong (λ X → G₁ g' ∘D X) (assoc D) ⟩
            G₁ g' ∘D ((G₁ f' ∘D (h ∘D F₁ f)) ∘D F₁ g) 
              ≡⟨⟩
            W₁ (g ,' g') (W₁ (f ,' f') h) ∎
      
      open Functor W renaming ( id to W-id ; compose to W-compose ; F₀ to W₀ ; F₁ to W₁ )
  
      W-wedge : (X : Obj (Set' {ℓD₁}))
              → (τ : (c : Obj C) → X → W₀ (c ,' c)) 
              → (natural : (c c' : Obj C) → (f : Hom C c c') → (x : X) → τ c' x ∘D F₁ f ≡ G₁ f ∘D τ c x)
              → Wedge X W
      W-wedge X τ natural
        = wedge τ $ λ {c} {c'} (f : Hom C c c') → fun-ext $ λ (x : X) → begin
          W₁ (f ,' id C) (τ c' x) 
            ≡⟨⟩
          G₁ (id C) ∘D (τ c' x ∘D F₁ f) 
            ≡⟨ cong (λ Y → Y ∘D (τ c' x ∘D F₁ f)) G-id ⟩
          id D ∘D (τ c' x ∘D F₁ f) 
            ≡⟨ right-id D ⟩
          τ c' x ∘D F₁ f
            ≡⟨ natural c c' f x ⟩
          G₁ f ∘D τ c x
            ≡⟨ cong (λ Y → G₁ f ∘D Y) (sym $ left-id D) ⟩
          G₁ f ∘D (τ c x ∘D id D)
            ≡⟨ cong (λ Y → G₁ f ∘D (τ c x ∘D Y)) (sym F-id) ⟩
          G₁ f ∘D (τ c x ∘D F₁ (id C))
            ≡⟨⟩
          W₁ (id C ,' f) (τ c x) ∎

  
      natTransEnd : (X : Obj (Set' {ℓD₁}))
                  → (τ : (c : Obj C) → X → W₀ (c ,' c)) 
                  → (natural : (c c' : Obj C) → (f : Hom C c c') → (x : X) → τ c' x ∘D F₁ f ≡ G₁ f ∘D τ c x)
                  → End W
      natTransEnd X τ natural = record { w = X ; e = W-wedge X τ natural ; universal = universal }
        where
          universal : {X' : Obj Set'} (e' : Wedge X' W) → ∃ (λ f → IsUnique f × e' ≡ Wedge.compose (W-wedge X τ natural) f)
          universal {X'} e' = (λ x' → {!!}) ,' {!!} ,' (wedge-eq $ {!!})

      natTransHomSetToNatTransEnd : Hom ([ C , D ]) F G → End W
      natTransHomSetToNatTransEnd NatTrans = record { w = {!NatTrans!} ; e = {!!} ; universal = {!!} }
 
  open NatTransEnd public
