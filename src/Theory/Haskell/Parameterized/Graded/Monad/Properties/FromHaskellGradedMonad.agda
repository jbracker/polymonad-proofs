
open import Level
open import Function hiding ( id ; _∘_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
open ≅-Reasoning renaming ( begin_ to hbegin_ ; _∎ to _∎h ) hiding ( _≡⟨⟩_ ; _≡⟨_⟩_ )

open import Extensionality
open import Haskell hiding ( Hask )
open import Haskell.Parameterized.Graded.Monad renaming ( GradedMonad to HaskellGradedMonad )
open import Theory.Monoid
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Graded.Monad

module Theory.Haskell.Parameterized.Graded.Monad.Properties.FromHaskellGradedMonad where

private
  Hask = setCategory {zero}

HaskellGradedMonad→GradedMonad : {ℓMon : Level} {Mon : Set ℓMon} {monoid : Monoid Mon}
                               → (Σ (Mon → TyCon) (HaskellGradedMonad monoid))
                               → (Σ (Mon → Functor Hask Hask) (GradedMonad monoid))
HaskellGradedMonad→GradedMonad {ℓMon} {Mon} {monoid} (M , monad) 
  = F , graded-monad η μ μ-coher η-left-coher η-right-coher
  where
    open Monoid monoid
    open HaskellGradedMonad monad
    open Category Hask hiding ( left-id ; right-id ; assoc )
    open NaturalTransformation renaming ( η to nat-η )
    
    F : Mon → Functor Hask Hask
    F i = HaskellFunctor→Functor (functor i)

    ε≅ε∙ε : ε ≅ ε ∙ ε
    ε≅ε∙ε = hsym $ ≡-to-≅ $ Monoid.left-id monoid

    hfe : {ℓ : Level} {X : Set ℓ} {α : Type} {i j : Mon} → (i ≡ j) → (λ (_ : X) → M i α) ≅ (λ (_ : X) → M j α)
    hfe {ℓ} {X} {α} p = hcong (λ Y → (λ (_ : X) → M Y α)) (≡-to-≅ p)

    gcong : {α β : Type} {i j : Mon} {f : α → M i β} {g : α → M j β} → i ≡ j → f ≅ g → ((α → M i β) ∋ f) ≅ ((α → M j β) ∋ g)
    gcong refl hrefl = hrefl
    
    gcong' : {α : Type} {i j : Mon} {m : M i α} {n : M j α} → i ≡ j → m ≅ n → (M i α ∋ m) ≅ (M j α ∋ n)
    gcong' refl hrefl = hrefl
    
    η : NaturalTransformation Id[ Hask ] (F ε)
    η = naturalTransformation (λ α → return {α}) $ λ {α β} {f} → ≅-to-≡ $ hbegin
      ((α → M ε β) ∋ (fmap f ∘ return))
        ≅⟨ hcong₂ (λ X Y → (α → M X β) ∋ Y) ε≅ε∙ε (het-fun-ext (hfe $ sym $ left-id) ((λ ma → hsym (law-monad-fmap f (return ma))))) ⟩
      ((α → M (ε ∙ ε) β) ∋ (λ ma → (return ma) >>= (return ∘ f)))
        ≅⟨ hcong₂ (λ X Y → (α → M X β) ∋ Y) (hsym ε≅ε∙ε) (het-fun-ext ((hcong (λ X → (λ _ → M X β)) (hsym ε≅ε∙ε))) (λ ma → law-left-id ma (return ∘ f))) ⟩
      ((α → M ε β) ∋ (return ∘ f)) ∎h
    
    μ : {i j : Mon} → NaturalTransformation [ F i ]∘[ F j ] (F (i ∙ j))
    μ {i} {j} = naturalTransformation (λ α → join {α} {i} {j}) $ λ {α β} {f : α → β} → ≅-to-≡ $ hbegin
      ((M i (M j α) → M (i ∙ j) β) ∋ (fmap f ∘ join))
        ≅⟨ hrefl ⟩
      ((M i (M j α) → M (i ∙ j) β) ∋ (λ ma → fmap f (ma >>= id)))
        ≅⟨ gcong (sym right-id) (het-fun-ext (hfe $ sym right-id) ((λ ma → hsym $ law-monad-fmap f (ma >>= id)))) ⟩
      ((M i (M j α) → M ((i ∙ j) ∙ ε) β) ∋ (λ ma → (ma >>= id) >>= (return ∘ f)))
        ≅⟨ gcong (sym assoc) (het-fun-ext (hfe $ sym assoc) ((λ ma → hsym (law-assoc ma id (return ∘ f))))) ⟩
      ((M i (M j α) → M (i ∙ (j ∙ ε)) β) ∋ (λ ma → ma >>= (λ x → x >>= (return ∘ f))))
        ≅⟨ gcong (cong (_∙_ i) (sym left-id))
                 (het-fun-ext (hfe $ cong (_∙_ i) $ sym left-id) 
                              (λ ma → hcong₂ (λ X Y → M (i ∙ X) β ∋ ma >>= Y) 
                                             (≡-to-≅ $ sym $ left-id) 
                                             (het-fun-ext (hfe (sym left-id)) (λ x → hsym (law-left-id (x >>= (return ∘ f)) id))))) ⟩
      ((M i (M j α) → M (i ∙ (ε ∙ (j ∙ ε))) β) ∋ (λ ma → ma >>= (λ x → return (x >>= (return ∘ f)) >>= id)))
        ≅⟨ gcong assoc (het-fun-ext (hfe assoc) (λ ma → law-assoc ma (λ a → return (a >>= (return ∘ f))) id)) ⟩
      ((M i (M j α) → M ((i ∙ ε) ∙ (j ∙ ε)) β) ∋ (λ ma → (ma >>= (λ a → return (a >>= (return ∘ f)))) >>= id))
        ≅⟨ gcong (cong (_∙_ (i ∙ ε)) right-id) 
                 (het-fun-ext (hfe (cong (_∙_ (i ∙ ε)) right-id)) 
                              (λ ma → hcong₂ (λ X Y → M ((i ∙ ε) ∙ X) β ∋ (ma >>= (return ∘ Y)) >>= id) 
                                             (≡-to-≅ right-id) 
                                             (het-fun-ext (hfe right-id) (λ x → law-monad-fmap f x)))) ⟩
      ((M i (M j α) → M ((i ∙ ε) ∙ j) β) ∋ (λ ma → (ma >>= (return ∘ (fmap f))) >>= id))
        ≅⟨ gcong (cong (λ X → X ∙ j) right-id) 
                 (het-fun-ext (hfe (cong (λ X → X ∙ j) right-id)) 
                              (λ ma → hcong₂ (λ X Y → M (X ∙ j) β ∋ Y >>= id) 
                                             (≡-to-≅ right-id)
                                             (law-monad-fmap (fmap f) ma))) ⟩
      ((M i (M j α) → M (i ∙ j) β) ∋ (λ ma → (fmap (fmap f) ma) >>= id))
        ≅⟨ hrefl ⟩
      ((M i (M j α) → M (i ∙ j) β) ∋ (join ∘ fmap (fmap f))) ∎h
    
    abstract
      μ-coher : {i j k : Mon} {x : Type}
              → nat-η (μ {i} {j ∙ k}) x ∘ [ F i ]₁ (nat-η (μ {j} {k}) x) 
              ≅ nat-η (μ {i ∙ j} {k}) x ∘ nat-η (μ {i} {j}) ([ F k ]₀ x)
      μ-coher {i} {j} {k} {α} = hbegin
        ((M i (M j (M k α)) → M (i ∙ (j ∙ k)) α) ∋ (join ∘ fmap join))
          ≅⟨ hrefl ⟩
        ((M i (M j (M k α)) → M (i ∙ (j ∙ k)) α) ∋ (λ ma → (fmap (λ a → a >>= id) ma) >>= id))
          ≅⟨ gcong (cong (λ X → X ∙ (j ∙ k)) (sym right-id)) 
                   (het-fun-ext (hfe (cong (λ X → X ∙ (j ∙ k)) (sym right-id))) 
                                (λ ma → hcong₂ (λ X Y → M (X ∙ (j ∙ k)) α ∋ Y >>= id) 
                                               (≡-to-≅ (sym right-id)) 
                                               (hsym (law-monad-fmap (λ a → a >>= id) ma)))) ⟩
        ((M i (M j (M k α)) → M ((i ∙ ε) ∙ (j ∙ k)) α) ∋ (λ ma → (ma >>= (return ∘ (λ a → a >>= id))) >>= id))
          ≅⟨ gcong (sym assoc) (het-fun-ext (hfe (sym assoc)) (λ ma → hsym $ law-assoc ma (return ∘ (λ a → a >>= id)) id)) ⟩
        ((M i (M j (M k α)) → M (i ∙ (ε ∙ (j ∙ k))) α) ∋ (λ ma → ma >>= (λ x → return (x >>= id) >>= id)))
          ≅⟨ gcong (cong (_∙_ i) left-id) 
                   (het-fun-ext (hfe (cong (_∙_ i) left-id)) 
                                (λ ma → hcong₂ (λ X Y → M (i ∙ X) α ∋ ma >>= Y) 
                                               (≡-to-≅ left-id) 
                                               (het-fun-ext (hfe left-id) (λ x → law-left-id (x >>= id) id)))) ⟩
        ((M i (M j (M k α)) → M (i ∙ (j ∙ k)) α) ∋ (λ ma → ma >>= (λ x → x >>= id)))
          ≅⟨ gcong assoc (het-fun-ext (hfe assoc) (λ ma → law-assoc ma id id)) ⟩
        ((M i (M j (M k α)) → M ((i ∙ j) ∙ k) α) ∋ (λ ma → (ma >>= id) >>= id))
          ≅⟨ hrefl ⟩
        ((M i (M j (M k α)) → M ((i ∙ j) ∙ k) α) ∋ (join ∘ join)) ∎h
    
    abstract
      η-left-coher : {i : Mon} {x : Type}
                   → nat-η (μ {i} {ε}) x ∘ [ F i ]₁ (nat-η η x) ≅ nat-η (Id⟨ F i ⟩) x
      η-left-coher {i} {α} = hbegin
        ((M i α → M (i ∙ ε) α) ∋ (join ∘ fmap return))
          ≅⟨ hrefl ⟩
        ((M i α → M (i ∙ ε) α) ∋ (λ ma → fmap return ma >>= id))
          ≅⟨ gcong (sym right-id) 
                   (het-fun-ext (hfe (sym right-id)) 
                                (λ ma → hcong₂ (λ X Y → M (X ∙ ε) α ∋ Y >>= id) 
                                               (≡-to-≅ (sym right-id)) 
                                               (hsym $ law-monad-fmap return ma))) ⟩
        ((M i α → M ((i ∙ ε) ∙ ε) α) ∋ (λ ma → (ma >>= (return ∘ return)) >>= id))
          ≅⟨ gcong (sym assoc) (het-fun-ext (hfe (sym assoc)) (λ ma → hsym (law-assoc ma (return ∘ return) id))) ⟩
        ((M i α → M (i ∙ (ε ∙ ε)) α) ∋ (λ ma → ma >>= (λ x → return (return x) >>= id)))
          ≅⟨ gcong (cong (_∙_ i) left-id) 
                   (het-fun-ext (hfe $ cong (_∙_ i) left-id) 
                                (λ ma → hcong₂ (λ X Y → M (i ∙ X) α ∋ ma >>= Y) 
                                               (≡-to-≅ left-id) 
                                               (het-fun-ext (hfe left-id) (λ x → law-left-id (return x) id)))) ⟩
        ((M i α → M (i ∙ ε) α) ∋ (λ ma → ma >>= return))
          ≅⟨ gcong right-id (het-fun-ext (hfe right-id) law-right-id) ⟩
        ((M i α → M i α) ∋ id) ∎h
    
    abstract
      η-right-coher : {i : Mon} {x : Type}
                    → nat-η (μ {ε} {i}) x ∘ nat-η η ([ F i ]₀ x) ≅ nat-η (Id⟨ F i ⟩) x
      η-right-coher {i} {α} = hbegin
        ((M i α → M (ε ∙ i) α) ∋ (join ∘ return))
          ≅⟨ hrefl ⟩ 
        ((M i α → M (ε ∙ i) α) ∋ (λ ma → return ma >>= id))
          ≅⟨ gcong left-id (het-fun-ext (hfe left-id) (λ ma → law-left-id ma id)) ⟩
        ((M i α → M i α) ∋ id) ∎h

