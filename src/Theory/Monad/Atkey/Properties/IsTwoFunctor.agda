
module Theory.Monad.Atkey.Properties.IsTwoFunctor where

open import Theory.TwoFunctor.Properties.FromAtkeyParameterizedMonad using ( AtkeyParameterizedMonad→LaxTwoFunctor ) public

{-
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product renaming ( _,_ to _,'_ )
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality 
  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Haskell
open import Theory.Triple
open import Theory.Category
open import Theory.Functor
open import Theory.Functor.Composition
open import Theory.Natural.Transformation renaming (NaturalTransformation to NatTrans)
open import Theory.Monad.Atkey
open import Theory.TwoCategory
open import Theory.TwoCategory.Examples
open import Theory.TwoFunctor 

open Category
open StrictTwoCategory

AtkeyParameterizedMonad→LaxTwoFunctor
  : {ℓC₀ ℓC₁ ℓS₀ ℓS₁ : Level} 
  → {C : Category {ℓC₀} {ℓC₁}} {S : Category {ℓS₀} {ℓS₁}}
  → {M : Functor (S op ×C S ×C C) C}
  → AtkeyParameterizedMonad C S M
  → LaxTwoFunctor (Category→StrictTwoCategory S) (functorTwoCategory {ℓC₀} {ℓC₁})
AtkeyParameterizedMonad→LaxTwoFunctor {ℓC₀} {ℓC₁} {ℓS₀} {ℓS₁} {C} {S} {M} monad = record
  { P₀ = P₀
  ; P₁ = P₁
  ; η = η
  ; μ = λ {s₁} {s₂} {s₃} {f} {g} → μ {s₁} {s₂} {s₃} {f} {g}
  ; laxFunId₁ = λ {s₁} {s₂} {f} → laxFunId₁ {s₁} {s₂} {f}
  ; laxFunId₂ = λ {s₁} {s₂} {f} → laxFunId₂ {s₁} {s₂} {f}
  ; laxFunAssoc = λ {s₀} {s₁} {s₂} {s₃} {f} {g} {h} → natural-transformation-eq $ fun-ext $ laxFunAssoc {s₀} {s₁} {s₂} {s₃} {f} {g} {h}
  } where
    FunTwoCat = functorTwoCategory {ℓC₀} {ℓC₁}
    S2 = Category→StrictTwoCategory S

    _∘C_ = _∘_ C ; _∘S_ = _∘_ S ; _∘Sop_ = _∘_ (S op)
    
    P₀ : Cell₀ S2 → Cell₀ FunTwoCat
    P₀ _ = C
    
    P₁ : {s₁ s₂ : Obj S} → Functor (HomCat S2 s₁ s₂) (HomCat FunTwoCat (P₀ s₁) (P₀ s₂))
    P₁ {s₁} {s₂} = record 
      { F₀ = F₀ 
      ; F₁ = λ {a} {b} → F₁ {a} {b}
      ; id = refl
      ; compose = λ {a} {b} {c} {f} {g} → compose {a} {b} {c} {f} {g} 
      } where
        _∘SS_ = _∘_ (HomCat S2 s₁ s₂)
        _∘CC_ = _∘_ (HomCat FunTwoCat C C)
        
        F₀₀ :  Obj C → Obj C
        F₀₀ a = [ M ]₀ (s₂ , s₁ , a)
        
        F₀₁ : {a b : Obj C} → Hom C a b → Hom C (F₀₀ a) (F₀₀ b)
        F₀₁ f = [ M ]₁ (id (S op) {s₂} , id S {s₁} , f)
 
        compose₀ : {a b c : Obj C} 
                 → {f : Hom C a b} {g : Hom C b c} 
                 → [ M ]₁ (id (S op) {s₂} , id S {s₁} , (g ∘C f)) 
                 ≡ [ M ]₁ (id (S op) {s₂} , id S {s₁} , g) ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , f)
        compose₀ {a} {b} {c} {f} {g} = begin
          [ M ]₁ (id (S op) {s₂} , id S {s₁} , (g ∘C f)) 
            ≡⟨ cong₂ (λ X Y → [ M ]₁ (X , Y , (g ∘C f))) (sym $ left-id (S op)) (sym $ left-id S) ⟩
          [ M ]₁ ((id (S op) {s₂} ∘Sop id (S op) {s₂}) , (id S {s₁} ∘S id S {s₁}) , (g ∘C f))
            ≡⟨ Functor.compose M ⟩
          [ M ]₁ (id (S op) {s₂} , id S {s₁} , g) ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , f) ∎

        F₀ : Hom S s₁ s₂ → Functor (P₀ s₁) (P₀ s₂)
        F₀ f = functor F₀₀ F₀₁ (Functor.id M) compose₀
        
        F₁ : {a b : Hom S s₁ s₂} 
           → Hom (HomCat S2 s₁ s₂) a b
           → Hom (HomCat FunTwoCat (P₀ s₁) (P₀ s₂)) (F₀ a) (F₀ b)
        F₁ {a} {b} tt = naturalTransformation (λ x → id C {[ F₀ a ]₀ x}) (trans (left-id C) (sym $ right-id C))
        
        compose : {a b c : Hom S s₁ s₂}
                → {f : Hom (HomCat S2 s₁ s₂) a b} {g : Hom (HomCat S2 s₁ s₂) b c}
                → F₁ {a} {c} (_∘SS_ {a} {b} {c} g f) ≡ (F₁ {a} {b} g) ∘CC (F₁ {b} {c} f)
        compose {a} {b} {c} {tt} {tt} = natural-transformation-eq $ fun-ext $ λ (x : Obj C) → sym (right-id C)
    
    η : {s : Obj S} → NatTrans Id[ C ] ([ P₁ {s} {s} ]₀ (id S {s}))
    η {s} = naturalTransformation (λ x → AtkeyParameterizedMonad.η monad {x} {s}) (AtkeyParameterizedMonad.naturalη monad {s})
    
    μ : {s₁ s₂ s₃ : Obj S} {f : Hom S s₁ s₂} {g : Hom S s₂ s₃}
      → NatTrans [ [ P₁ ]₀ g ]∘[ [ P₁ ]₀ f ] ([ P₁ ]₀ (g ∘S f))
    μ {s₁} {s₂} {s₃} {f} {g} = naturalTransformation (λ x → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₁}) (AtkeyParameterizedMonad.naturalμ monad {s₃} {s₂} {s₁})
    
    laxFunId₁ : {s₁ s₂ : Obj S} {f : Hom S s₁ s₂}
              → ⟨ Functor.F₁ (P₁ {s₁} {s₂}) {f} {f} (λ' S2 f) ⟩∘ᵥ⟨ ⟨ μ {s₁} {s₁} {s₂} {id S {s₁}} {f} ⟩∘ᵥ⟨ ⟨ id₂ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f} ⟩∘ₕ⟨ η {s₁} ⟩ ⟩ ⟩
              ≡ λ' FunTwoCat ([ P₁ {s₁} {s₂} ]₀ f)
    laxFunId₁ {s₁} {s₂} {f} = natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
      NatTrans.η (⟨ Functor.F₁ (P₁ {s₁} {s₂}) {f} {f} (λ' S2 f) ⟩∘ᵥ⟨ ⟨ μ {s₁} {s₁} {s₂} {id S {s₁}} {f} ⟩∘ᵥ⟨ ⟨ id₂ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f} ⟩∘ₕ⟨ η {s₁} ⟩ ⟩ ⟩) x
        ≡⟨ refl ⟩
      id C {[ M ]₀ (s₂ , s₁ , x)} ∘C (NatTrans.η (μ {s₁} {s₁} {s₂} {id S {s₁}} {f}) x 
                                  ∘C (id C {[ M ]₀ (s₂ , s₁ , [ M ]₀ (s₁ , s₁ , x))}
                                  ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , NatTrans.η (η {s₁}) x) ) )
        ≡⟨ right-id C ⟩
      NatTrans.η (μ {s₁} {s₁} {s₂} {id S {s₁}} {f}) x ∘C (Category.id C {[ M ]₀ (s₂ , s₁ , [ M ]₀ (s₁ , s₁ , x))}
                                                      ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , NatTrans.η (η {s₁}) x) )
        ≡⟨ cong (λ X → NatTrans.η (μ {s₁} {s₁} {s₂} {id S {s₁}} {f}) x ∘C X) (right-id C) ⟩
      NatTrans.η (μ {s₁} {s₁} {s₂} {id S {s₁}} {f}) x ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , NatTrans.η (η {s₁}) x)
        ≡⟨ refl ⟩
      AtkeyParameterizedMonad.μ monad {x} {s₂} {s₁} {s₁} ∘C [ M ]₁ (id (S op) {s₂} , id S {s₁} , AtkeyParameterizedMonad.η monad {x} {s₁})
        ≡⟨ AtkeyParameterizedMonad.left-id monad {x} {s₂} {s₁} ⟩
      id C {[ [ P₁ {s₁} {s₂} ]₀ f ]₀ x}
        ≡⟨ refl ⟩
      NatTrans.η Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩ x
        ≡⟨ ≅-to-≡ $ subst₂-insert (sym $ hIdL₁ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f}) refl (Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩) x ⟩
      NatTrans.η (subst₂ NatTrans (sym $ hIdL₁ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f}) refl (Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩)) x
        ≡⟨ refl ⟩
      NatTrans.η (lUnitor FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f}) x ∎
    
    laxFunId₂ : {s₁ s₂ : Obj S} {f : Hom S s₁ s₂} 
      → ⟨ Functor.F₁ (P₁ {s₁} {s₂}) {f} {f} (ρ S2 f) ⟩∘ᵥ⟨ ⟨ μ {s₁} {s₂} {s₂} {f} {id S {s₂}} ⟩∘ᵥ⟨ ⟨ η {s₂} ⟩∘ₕ⟨ id₂ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f} ⟩ ⟩ ⟩
      ≡ ρ FunTwoCat ([ P₁ {s₁} {s₂} ]₀ f)
    laxFunId₂ {s₁} {s₂} {f} = natural-transformation-eq $ fun-ext $ λ (x : Obj C) → begin
      NatTrans.η ⟨ Functor.F₁ (P₁ {s₁} {s₂}) {f} {f} (ρ S2 f) ⟩∘ᵥ⟨ ⟨ μ {s₁} {s₂} {s₂} {f} {id S {s₂}} ⟩∘ᵥ⟨ ⟨ η {s₂} ⟩∘ₕ⟨ id₂ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f} ⟩ ⟩ ⟩ x
        ≡⟨ refl ⟩
      id C {[ M ]₀ (s₂ , s₁ , x)} ∘C (NatTrans.η (μ {s₁} {s₂} {s₂} {f} {id S {s₂}}) x 
                                  ∘C (NatTrans.η (η {s₂}) ([ M ]₀ (s₂ , s₁ , x)) 
                                  ∘C Category.id C {[ M ]₀ (s₂ , s₁ , x)} ) )
        ≡⟨ right-id C ⟩
      NatTrans.η (μ {s₁} {s₂} {s₂} {f} {id S {s₂}}) x ∘C (NatTrans.η (η {s₂}) ([ M ]₀ (s₂ , s₁ , x)) 
                                                      ∘C Category.id C {[ M ]₀ (s₂ , s₁ , x)} )
        ≡⟨ cong (λ X → NatTrans.η (μ {s₁} {s₂} {s₂} {f} {id S {s₂}}) x ∘C X) (left-id C) ⟩
      NatTrans.η (μ {s₁} {s₂} {s₂} {f} {id S {s₂}}) x ∘C NatTrans.η (η {s₂}) ([ M ]₀ (s₂ , s₁ , x))
        ≡⟨ refl ⟩
      AtkeyParameterizedMonad.μ monad {x} {s₂} {s₂} {s₁} ∘C AtkeyParameterizedMonad.η monad {[ M ]₀ (s₂ , s₁ , x)} {s₂}
        ≡⟨ AtkeyParameterizedMonad.right-id monad {x} {s₂} {s₁}  ⟩
      id C {[ M ]₀ (s₂ , s₁ , x)}
        ≡⟨ refl ⟩
      NatTrans.η Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩ x
        ≡⟨ ≅-to-≡ $ subst₂-insert (sym $ hIdR₁ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f}) refl (Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩) x ⟩
      NatTrans.η (subst₂ NatTrans (sym $ hIdR₁ FunTwoCat {C} {C} {[ P₁ {s₁} {s₂} ]₀ f}) refl (Id⟨ [ P₁ {s₁} {s₂} ]₀ f ⟩)) x
        ≡⟨ refl ⟩
      NatTrans.η (ρ FunTwoCat {C} {C} ([ P₁ {s₁} {s₂} ]₀ f)) x ∎ 

    laxFunAssoc : {s₀ s₁ s₂ s₃ : Obj S}
                → {f : Hom S s₀ s₁} {g : Hom S s₁ s₂} {h : Hom S s₂ s₃}
                → (x : Obj C)
                → id C {[ M ]₀ (s₃ , s₀ , x)}
                    ∘C ( AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₀}
                    ∘C ( id C {[ M ]₀ (s₃ , s₂ , ([ M ]₀ (s₂ , s₀ , x)))} 
                    ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , AtkeyParameterizedMonad.μ monad {x} {s₂} {s₁} {s₀}) ) )
                ≡ AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
                    ∘C ( ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) )
                    ∘C NatTrans.η (subst₂ NatTrans refl (hAssoc₁ FunTwoCat {C} {C} {C} {C} {[ P₁ {s₀} {s₁} ]₀ f} {[ P₁ {s₁} {s₂} ]₀ g} {[ P₁ {s₂} {s₃} ]₀ h}) 
                                                        (Id⟨ [ [ P₁ {s₂} {s₃} ]₀ h ]∘[ [ [ P₁ {s₁} {s₂} ]₀ g ]∘[ [ P₁ {s₀} {s₁} ]₀ f ] ] ⟩)) x)
    laxFunAssoc {s₀} {s₁} {s₂} {s₃} {f} {g} {h} x = begin
      id C {[ M ]₀ (s₃ , s₀ , x)}
        ∘C ( AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₀}
        ∘C ( id C {[ M ]₀ (s₃ , s₂ , ([ M ]₀ (s₂ , s₀ , x)))} 
        ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , AtkeyParameterizedMonad.μ monad {x} {s₂} {s₁} {s₀}) ) )
        ≡⟨ right-id C ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₀}
        ∘C ( id C {[ M ]₀ (s₃ , s₂ , ([ M ]₀ (s₂ , s₀ , x)))} 
        ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , AtkeyParameterizedMonad.μ monad {x} {s₂} {s₁} {s₀}) )
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₀} ∘C X) (right-id C) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₂} {s₀}
        ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , AtkeyParameterizedMonad.μ monad {x} {s₂} {s₁} {s₀})
        ≡⟨ AtkeyParameterizedMonad.assoc monad ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁}
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀} ∘C X) (sym $ left-id C) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C id C )
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀} ∘C ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C X)) (sym $ Functor.id M) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , id C ) )
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀} ∘C ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , X ) )) (sym $ Functor.id M) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) )
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀} ∘C X) (sym $ left-id C) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) )
        ∘C Category.id C {[ [ [ P₁ {s₂} {s₃} ]₀ h ]∘[ [ [ P₁ {s₁} {s₂} ]₀ g ]∘[ [ P₁ {s₀} {s₁} ]₀ f ] ] ]₀ x} )
        ≡⟨ refl ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) )
        ∘C NatTrans.η (Id⟨ [ [ P₁ {s₂} {s₃} ]₀ h ]∘[ [ [ P₁ {s₁} {s₂} ]₀ g ]∘[ [ P₁ {s₀} {s₁} ]₀ f ] ] ⟩) x)
        ≡⟨ cong (λ X → AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
                       ∘C ( ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) ) ∘C X)) 
                (≅-to-≡ $ subst₂-insert refl 
                                        (hAssoc₁ FunTwoCat {C} {C} {C} {C} {[ P₁ {s₀} {s₁} ]₀ f} {[ P₁ {s₁} {s₂} ]₀ g} {[ P₁ {s₂} {s₃} ]₀ h}) 
                                        (Id⟨ [ [ P₁ {s₂} {s₃} ]₀ h ]∘[ [ [ P₁ {s₁} {s₂} ]₀ g ]∘[ [ P₁ {s₀} {s₁} ]₀ f ] ] ⟩) x) ⟩ 
      AtkeyParameterizedMonad.μ monad {x} {s₃} {s₁} {s₀}
        ∘C ( ( AtkeyParameterizedMonad.μ monad {[ M ]₀ (s₁ , s₀ , x)} {s₃} {s₂} {s₁} ∘C [ M ]₁ (id (S op) {s₃} , id S {s₂} , [ M ]₁ (id (S op) {s₂} , id S {s₁} , id C {[ M ]₀ (s₁ , s₀ , x)} ) ) )
        ∘C NatTrans.η (subst₂ NatTrans refl (hAssoc₁ FunTwoCat {C} {C} {C} {C} {[ P₁ {s₀} {s₁} ]₀ f} {[ P₁ {s₁} {s₂} ]₀ g} {[ P₁ {s₂} {s₃} ]₀ h}) 
                                            (Id⟨ [ [ P₁ {s₂} {s₃} ]₀ h ]∘[ [ [ P₁ {s₁} {s₂} ]₀ g ]∘[ [ P₁ {s₀} {s₁} ]₀ f ] ] ⟩)) x) ∎
-}
