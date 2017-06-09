
open import Level
open import Function renaming ( _∘_ to _∘F_ ) hiding ( id )

open import Data.Unit
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

      SetW = Set' {ℓD₁}
  
      open Functor F renaming ( id to F-id ; compose to F-compose )
      open Functor G renaming ( id to G-id ; compose to G-compose ; F₀ to G₀ ; F₁ to G₁ )
  
      W : Functor C×C SetW
      W = functor W₀ W₁ W-id W-compose
        where
          W₀ : Obj C×C → Obj SetW
          W₀ (c ,' c') = Hom D (F₀ c) (G₀ c')
      
          W₁ : {a b : Obj C×C} → Hom C×C a b → Hom SetW (W₀ a) (W₀ b)
          W₁ {a} {b} (f ,' g) h = G₁ g ∘D (h ∘D F₁ f)
          
          W-id : {a : Obj C×C} → W₁ (id C×C {a}) ≡ id SetW
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
  
      NatTrans→Wedge : NaturalTransformation F G → Wedge (Lift ⊤) W
      NatTrans→Wedge α = wedge ∫ coher
        where 
          ∫ : (c : Obj C) → Lift ⊤ → W₀ (c ,' c)
          ∫ c (lift tt) = NaturalTransformation.η α c
          
          ∫' = λ c → ∫ c (lift tt)
          
          coher : {c c' : Obj C} (f : Hom C c c') → W₁ (f ,' id C) ∘F ∫ c' ≡ W₁ (id C ,' f) ∘F ∫ c
          coher {c} {c'} f = fun-ext $ λ _ → begin
            W₁ (f ,' id C) (∫' c') 
              ≡⟨⟩
            G₁ (id C) ∘D (∫' c' ∘D F₁ f) 
              ≡⟨ cong (λ Y → Y ∘D (∫' c' ∘D F₁ f)) G-id ⟩
            id D ∘D (∫' c' ∘D F₁ f) 
              ≡⟨ right-id D ⟩
            ∫' c' ∘D F₁ f
              ≡⟨ sym $ NaturalTransformation.natural α ⟩
            G₁ f ∘D ∫' c
              ≡⟨ cong (λ Y → G₁ f ∘D Y) (sym $ left-id D) ⟩
            G₁ f ∘D (∫' c ∘D id D)
              ≡⟨ cong (λ Y → G₁ f ∘D (∫' c ∘D Y)) (sym F-id) ⟩
            G₁ f ∘D (∫' c ∘D F₁ (id C))
              ≡⟨⟩
            W₁ (id C ,' f) (∫' c) ∎
      
      Wedge→NatTrans : Wedge (Lift ⊤) W → NaturalTransformation F G
      Wedge→NatTrans w = naturalTransformation η nat
        where
          η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
          η c = Wedge.e w c (lift tt)
          
          nat : {a b : Obj C} {f : Hom C a b} → [ G ]₁ f ∘D η a ≡ η b ∘D [ F ]₁ f
          nat {a} {b} {f} = begin
            G₁ f ∘D η a 
              ≡⟨ cong (λ Y → G₁ f ∘D Y) (sym $ left-id D) ⟩
            G₁ f ∘D (η a ∘D id D)
              ≡⟨ cong (λ Y → G₁ f ∘D (η a ∘D Y)) (sym F-id) ⟩
            G₁ f ∘D (η a ∘D F₁ (id C))
              ≡⟨⟩
            W₁ (id C ,' f) (η a)
              ≡⟨⟩
            W₁ (id C ,' f) (Wedge.e w a (lift tt))
              ≡⟨⟩
            (W₁ (id C ,' f) ∘F Wedge.e w a) (lift tt)
              ≡⟨ cong (λ X → X (lift tt)) (sym $ Wedge.coher w f) ⟩
            (W₁ (f ,' id C) ∘F Wedge.e w b) (lift tt)
              ≡⟨⟩
            W₁ (f ,' id C) (Wedge.e w b (lift tt))
              ≡⟨⟩
            W₁ (f ,' id C) (η b) 
               ≡⟨⟩
            G₁ (id C) ∘D (η b ∘D F₁ f) 
              ≡⟨ cong (λ Y → Y ∘D (η b ∘D F₁ f)) G-id ⟩
            id D ∘D (η b ∘D F₁ f) 
              ≡⟨ right-id D ⟩
            η b ∘D [ F ]₁ f ∎
      
      NatTransEnd : End W
      NatTransEnd = {!!}
        
      
      NatTrans→End : NaturalTransformation F G → End W
      NatTrans→End α = end {!!} e universal 
        where
          e : Wedge (Lift ⊤) W
          e = NatTrans→Wedge α 
          
          universal : {w' : Obj Set'} (e' : Wedge w' W) → ∃ (λ f → IsUnique f × Wedge.e e' ≡ Wedge.e (Wedge.compose (NatTrans→Wedge α) f))
          universal {w'} e' = (λ _ → lift tt) ,' unique-f ,' factor
            where
              unique-f : IsUnique (λ _ → lift tt)
              unique-f f = fun-ext (λ _ → refl)
              
              _∘Wedge_ = Wedge.compose (NatTrans→Wedge α)
              
              factor : Wedge.e e' ≡ Wedge.e (Wedge.compose (NatTrans→Wedge α) (λ _ → lift tt))
              factor = fun-ext $ λ (c : Obj C) → fun-ext $ λ x → begin
                Wedge.e e' c x 
                  ≡⟨ {!!} ⟩
                NaturalTransformation.η α c
                  ≡⟨⟩
                Wedge.e (NatTrans→Wedge α) c (lift tt)
                  ≡⟨⟩
                ((Wedge.e (NatTrans→Wedge α) c) ∘F (λ _ → lift tt)) x ∎
-- η : (x : Obj C) → Hom D ([ F ]₀ x) ([ G ]₀ x)
-- e : (c : Obj C) → Hom X w (F₀ F (c , c))
 {-
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
-} 
  open NatTransEnd public
