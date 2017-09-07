
-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; subst to hsubst ; subst₂ to hsubst₂ ; cong to hcong ; cong₂ to hcong₂ ; proof-irrelevance to hproof-irrelevance )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

-- Local
open import Extensionality
open import Congruence
open import Theory.Triple renaming ( _,_,_ to _,'_,'_ )
open import Theory.Category.Definition hiding ( category )
open import Theory.Functor.Definition
open import Theory.Natural.Transformation
open import Theory.TwoCategory.Definition

module Theory.TwoCategory.Equality where

open Category

strict-two-category-eq : {ℓ₀ ℓ₁ ℓ₂ : Level}
                       → {Cell₀₀ : Set ℓ₀}
                       → {Cell₀₁ : Set ℓ₀}
                       → {HomCat₀ : Cell₀₀ → Cell₀₀ → Category {ℓ₁} {ℓ₂}}
                       → {HomCat₁ : Cell₀₁ → Cell₀₁ → Category {ℓ₁} {ℓ₂}}
                       → {comp₀ : {a b c : Cell₀₀} → Functor (HomCat₀ b c ×C HomCat₀ a b) (HomCat₀ a c)}
                       → {comp₁ : {a b c : Cell₀₁} → Functor (HomCat₁ b c ×C HomCat₁ a b) (HomCat₁ a c)}
                       → {id₁₀ : {a : Cell₀₀} → Obj (HomCat₀ a a)}
                       → {id₁₁ : {a : Cell₀₁} → Obj (HomCat₁ a a)}
                       → {assoc₀ : {a b c d : Cell₀₀} {f : Obj (HomCat₀ a b)} {g : Obj (HomCat₀ b c)} {h : Obj (HomCat₀ c d)} 
                                 → [ comp₀ ]₀ (h , [ comp₀ ]₀ (g , f)) ≡ [ comp₀ ]₀ ([ comp₀ ]₀ (h , g) , f)}
                       → {assoc₁ : {a b c d : Cell₀₁} {f : Obj (HomCat₁ a b)} {g : Obj (HomCat₁ b c)} {h : Obj (HomCat₁ c d)} 
                                 → [ comp₁ ]₀ (h , [ comp₁ ]₀ (g , f)) ≡ [ comp₁ ]₀ ([ comp₁ ]₀ (h , g) , f)}
                       → {left-id₀ : {a b : Cell₀₀} {f : Obj (HomCat₀ a b)} → [ comp₀ ]₀ (f , id₁₀) ≡ f}
                       → {left-id₁ : {a b : Cell₀₁} {f : Obj (HomCat₁ a b)} → [ comp₁ ]₀ (f , id₁₁) ≡ f}
                       → {right-id₀ : {a b : Cell₀₀} {f : Obj (HomCat₀ a b)} → [ comp₀ ]₀ (id₁₀ , f) ≡ f}
                       → {right-id₁ : {a b : Cell₀₁} {f : Obj (HomCat₁ a b)} → [ comp₁ ]₀ (id₁₁ , f) ≡ f}
                       → {hli₀ : {a b : Cell₀₀} {f g : Obj (HomCat₀ a b)} {η : Hom (HomCat₀ a b) f g} → [ comp₀ ]₁ (η , id (HomCat₀ a a)) ≅ η}
                       → {hli₁ : {a b : Cell₀₁} {f g : Obj (HomCat₁ a b)} {η : Hom (HomCat₁ a b) f g} → [ comp₁ ]₁ (η , id (HomCat₁ a a)) ≅ η}
                       → {hri₀ : {a b : Cell₀₀} {f g : Obj (HomCat₀ a b)} {η : Hom (HomCat₀ a b) f g} → [ comp₀ ]₁ (id (HomCat₀ b b) , η) ≅ η}
                       → {hri₁ : {a b : Cell₀₁} {f g : Obj (HomCat₁ a b)} {η : Hom (HomCat₁ a b) f g} → [ comp₁ ]₁ (id (HomCat₁ b b) , η) ≅ η}
                       → {hassoc₀ : {a b c d : Cell₀₀} {f f' : Obj (HomCat₀ a b)} {g g' : Obj (HomCat₀ b c)} {h h' : Obj (HomCat₀ c d)} 
                                  → {η : Hom (HomCat₀ c d) h h'} {θ : Hom (HomCat₀ b c) g g'} {ι : Hom (HomCat₀ a b) f f'} 
                                  → [ comp₀ ]₁ (η , [ comp₀ ]₁ (θ , ι)) ≅ [ comp₀ ]₁ ([ comp₀ ]₁ (η , θ) , ι)}
                       → {hassoc₁ : {a b c d : Cell₀₁} {f f' : Obj (HomCat₁ a b)} {g g' : Obj (HomCat₁ b c)} {h h' : Obj (HomCat₁ c d)}
                                  → {η : Hom (HomCat₁ c d) h h'} {θ : Hom (HomCat₁ b c) g g'} {ι : Hom (HomCat₁ a b) f f'}
                                  → [ comp₁ ]₁ (η , [ comp₁ ]₁ (θ , ι)) ≅ [ comp₁ ]₁ ([ comp₁ ]₁ (η , θ) , ι)}
                       → (Cell₀₀ ≡ Cell₀₁)
                       → (HomCat₀ ≅ HomCat₁)
                       → ((λ {a b c} → comp₀ {a} {b} {c}) ≅ (λ {a b c} → comp₁ {a} {b} {c}))
                       → ((λ {a} → id₁₀ {a}) ≅ (λ {a} → id₁₁ {a}))
                       → strictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} Cell₀₀ HomCat₀ comp₀ id₁₀ assoc₀ left-id₀ right-id₀ hli₀ hri₀ hassoc₀ 
                       ≡ strictTwoCategory {ℓ₀} {ℓ₁} {ℓ₂} Cell₀₁ HomCat₁ comp₁ id₁₁ assoc₁ left-id₁ right-id₁ hli₁ hri₁ hassoc₁
strict-two-category-eq {ℓ₀} {ℓ₁} {ℓ₂} {Cell₀} {.Cell₀} {HomCat} {.HomCat} {comp} {.comp} {id₁} {.id₁} 
                       {assoc₀} {assoc₁} {li₀} {li₁} {ri₀} {ri₁} {hli₀} {hli₁} {hri₀} {hri₁} {hassoc₀} {hassoc₁} 
                       refl hrefl hrefl hrefl = cong₆ (strictTwoCategory Cell₀ HomCat comp id₁) p1 p2 p3 p4 p5 p6
  where
    p1 : (λ {a b c d} {f} {g} {h} → assoc₀ {a} {b} {c} {d} {f} {g} {h}) ≡ assoc₁
    p1 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ c → implicit-fun-ext 
       $ λ d → implicit-fun-ext 
       $ λ f → implicit-fun-ext 
       $ λ g → implicit-fun-ext 
       $ λ h → proof-irrelevance assoc₀ assoc₁
  
    p2 : (λ {a b} {f} → li₀ {a} {b} {f}) ≡ li₁
    p2 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance li₀ li₁
  
    p3 : (λ {a b} {f} → ri₀ {a} {b} {f}) ≡ ri₁
    p3 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → proof-irrelevance ri₀ ri₁
  
    p4 : (λ {a b} {f g} {η} → hli₀ {a} {b} {f} {g} {η}) ≡ hli₁
    p4 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → implicit-fun-ext 
       $ λ g → implicit-fun-ext 
       $ λ η → hproof-irrelevance hli₀ hli₁
  
    p5 : (λ {a b} {f g} {η} → hri₀ {a} {b} {f} {g} {η}) ≡ hri₁
    p5 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ f → implicit-fun-ext 
       $ λ g → implicit-fun-ext 
       $ λ η → hproof-irrelevance hri₀ hri₁
    
    p6 : (λ {a b c d} {f f'} {g g'} {h h'} {α} {β} {γ} → hassoc₀ {a} {b} {c} {d} {f} {f'} {g} {g'} {h} {h'} {α} {β} {γ}) ≡ hassoc₁
    p6 = implicit-fun-ext 
       $ λ a → implicit-fun-ext 
       $ λ b → implicit-fun-ext 
       $ λ c → implicit-fun-ext 
       $ λ d → implicit-fun-ext 
       $ λ f  → implicit-fun-ext 
       $ λ f' → implicit-fun-ext 
       $ λ g  → implicit-fun-ext 
       $ λ g' → implicit-fun-ext 
       $ λ h  → implicit-fun-ext 
       $ λ h' → implicit-fun-ext 
       $ λ α → implicit-fun-ext 
       $ λ β → implicit-fun-ext 
       $ λ γ → hproof-irrelevance hassoc₀ hassoc₁
