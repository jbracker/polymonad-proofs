

open import Level
open import Function

open import Data.Product renaming ( _,_ to _,'_ )

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; cong to hcong )
open ≡-Reasoning

open import Bijection renaming ( refl to brefl ; sym to bsym )
open import Equality
open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( functor-eq to hask-functor-eq )
open import Haskell.Parameterized.IndexedMonad

open import Theory.Triple
open import Theory.Category
open import Theory.Category.Examples
open import Theory.Functor hiding ( functor )
open import Theory.Monad.Atkey
open import Theory.Monad.Atkey.Equality
open import Theory.Monad.Atkey.FromIndexedMonad
open import Theory.Monad.Atkey.ToIndexedMonad

module Theory.Monad.Atkey.EquivalentIndexedMonad where

IxMonad↔AtkeyParameterizedMonad : {ℓ : Level} → (Ixs : Set ℓ)
                                → (∃ λ (M : Ixs → Ixs → TyCon) → IxMonad Ixs M) ↔ (AtkeyParameterizedMonad (Hask {zero}) (discreteCategory Ixs))
IxMonad↔AtkeyParameterizedMonad Ixs = bijection IxMonad→AtkeyParameterizedMonad' AtkeyParameterizedMonad→IxMonad' id₁ id₂
  where
    S = discreteCategory Ixs
    
    IxMonad→AtkeyParameterizedMonad' : ∃ (IxMonad Ixs) → AtkeyParameterizedMonad Hask S
    IxMonad→AtkeyParameterizedMonad' = (λ ∃IxMonad → IxMonad→AtkeyParameterizedMonad Ixs (proj₁ ∃IxMonad) (proj₂ ∃IxMonad))

    AtkeyParameterizedMonad→IxMonad' : AtkeyParameterizedMonad Hask S → (∃ λ (M : Ixs → Ixs → TyCon) → IxMonad Ixs M)
    AtkeyParameterizedMonad→IxMonad' monad = AtkeyFunctor→IxTyCon monad ,' AtkeyParameterizedMonad→IxMonad S monad
    
    id₁ : (m : AtkeyParameterizedMonad Hask S) → IxMonad→AtkeyParameterizedMonad' (AtkeyParameterizedMonad→IxMonad' m) ≡ m
    id₁ monad = atkey-parameterized-monad-eq eq-functor hrefl (≡-to-≅ eq-μ)
      where
        open AtkeyParameterizedMonad monad
        
        eq-T₁ : {a b : Category.Obj ((S op) ×C S ×C Hask)}
              → (f : Category.Hom ((S op) ×C S ×C Hask) a b)
              → Functor.F₁ (AtkeyParameterizedMonad.T (IxMonad→AtkeyParameterizedMonad' (AtkeyParameterizedMonad→IxMonad' monad))) {a} {b} f ≡ Functor.F₁ T {a} {b} f
        eq-T₁ {a₀ , a₁ , α} {.a₀ , .a₁ , β} (refl , refl , f) = fun-ext $ λ ma → refl
        
        eq-functor : AtkeyParameterizedMonad.T (IxMonad→AtkeyParameterizedMonad' (AtkeyParameterizedMonad→IxMonad' monad)) ≡ T
        eq-functor = functor-eq refl $ ≡-to-≅ $ implicit-fun-ext $ λ a → implicit-fun-ext $ λ b → fun-ext $ λ f → eq-T₁ {a} {b} f
        
        eq-μ : (λ {α} {i} {j} {k} → IxMonad.join (proj₂ (AtkeyParameterizedMonad→IxMonad' monad)) {α} {i} {j} {k}) ≡ μ
        eq-μ = implicit-fun-ext $ λ α → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext $ λ mma → begin
          IxMonad.join (proj₂ (AtkeyParameterizedMonad→IxMonad' monad)) mma
            ≡⟨⟩
          IxMonad._>>=_ (AtkeyParameterizedMonad→IxMonad S monad) mma (λ x → x)
            ≡⟨⟩
          μ ([ T ]₁ (refl , refl , (λ x → x)) mma)
            ≡⟨ cong (λ X → μ (X mma)) (Functor.id T) ⟩
          μ mma ∎
    
    id₂ : (m : ∃ (IxMonad Ixs)) → AtkeyParameterizedMonad→IxMonad' (IxMonad→AtkeyParameterizedMonad' m) ≡ m
    id₂ (M ,' monad) = Σ-eq refl $ ≡-to-≅ $ indexed-monad-eq eq-bind eq-return eq-functor
      where
        open IxMonad monad
        
        eq-bind : (λ {a} {b} {i} {j} {k} → IxMonad._>>=_ (proj₂ (AtkeyParameterizedMonad→IxMonad' (IxMonad→AtkeyParameterizedMonad' (M ,' monad)))) {a} {b} {i} {j} {k})  ≡ _>>=_
        eq-bind = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext $ λ ma → fun-ext $ λ f → begin
          IxMonad._>>=_ (proj₂ (AtkeyParameterizedMonad→IxMonad' (IxMonad→AtkeyParameterizedMonad' (M ,' monad)))) ma f
            ≡⟨⟩
          IxMonad._>>=_ (AtkeyParameterizedMonad→IxMonad S (IxMonad→AtkeyParameterizedMonad Ixs M monad)) ma f
            ≡⟨⟩
          join ([ IxTyCon→AtkeyFunctor Ixs M monad ]₁ (Category.id (S op) {i} , Category.id S {j} , f) ma)
            ≡⟨⟩
          (IxMonad.fmap monad f ma) >>= (λ x → x)
            ≡⟨ cong (λ X → _>>=_ X (λ x → x)) (sym (law-monad-fmap f ma)) ⟩
          (ma >>= (return ∘ f)) >>= (λ x → x)
            ≡⟨ sym (law-assoc ma (return ∘ f) (λ x → x)) ⟩
          ma >>= (λ a → return (f a) >>= (λ x → x))
            ≡⟨ cong (λ X → _>>=_ ma X) (fun-ext (λ a → law-right-id (f a) (λ x → x))) ⟩
          ma >>= f ∎
        
        eq-return : (λ {a} {i} → IxMonad.return (proj₂ (AtkeyParameterizedMonad→IxMonad' (IxMonad→AtkeyParameterizedMonad' (M ,' monad)))) {a} {i})  ≡ return
        eq-return = implicit-fun-ext $ λ α → implicit-fun-ext $ λ i → fun-ext $ λ a → refl
        
        eq-functor : IxMonad.functor (proj₂ (AtkeyParameterizedMonad→IxMonad' (IxMonad→AtkeyParameterizedMonad' (M ,' monad)))) ≡ IxMonad.functor monad
        eq-functor = fun-ext $ λ i → fun-ext $ λ j → hask-functor-eq refl

