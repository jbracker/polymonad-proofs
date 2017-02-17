
module Theory.Examples.HaskellMonadToMonad where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function renaming ( _∘_ to _∘F_ ; id to idF )
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary.HeterogeneousEquality 
--  renaming ( sym to hsym ; trans to htrans ; cong to hcong ; subst to hsubst ; subst₂ to hsubst₂ )
open ≡-Reasoning hiding ( _≅⟨_⟩_ )
--open ≅-Reasoning hiding ( _≡⟨_⟩_ ) renaming ( begin_ to hbegin_ ; _∎ to _∎h)

-- Local
open import Extensionality
open import Haskell
open import Haskell.Monad renaming ( Monad to HaskellMonad )
open import Haskell.Applicative renaming ( Applicative to HaskellApplicative )
open import Haskell.Functor renaming ( Functor to HaskellFunctor )
open import Theory.Category
open import Theory.Functor
open import Theory.NaturalTransformation renaming ( NaturalTransformation to NatTrans )
open import Theory.Monad hiding ( monad )
open import Theory.Examples.Category
open import Theory.Examples.HaskellFunctorToFunctor

HaskellMonad→Monad : {M : Type → Type}
                   → (monad : HaskellMonad M) 
                   → Monad (HaskellFunctor→Functor (HaskellApplicative.functor (HaskellMonad.applicative monad)))
HaskellMonad→Monad {M} monad = record 
  { η = NatTrans-η
  ; μ = NatTrans-μ
  ; μ-coher = μCoher
  ; η-left-coher = ηCoherL
  ; η-right-coher = ηCoherR
  } where
    C = setCategory {lzero}
    F = HaskellFunctor→Functor (Applicative.functor (Monad.applicative monad))
    
    open Category
    
    _∘C_ = _∘_ C
    
    _>>=_ = HaskellMonad._>>=_ monad
    join = HaskellMonad.join monad
    return = HaskellMonad.return monad
    fmap = HaskellFunctor.fmap (HaskellApplicative.functor (HaskellMonad.applicative monad))

    law-right-id = HaskellMonad.law-right-id monad
    law-left-id = HaskellMonad.law-left-id monad
    law-assoc = HaskellMonad.law-assoc monad
    law-monad-fmap = HaskellMonad.law-monad-fmap monad

    η : (α : Obj C) → Hom C ([ Id[ C ] ]₀ α) ([ F ]₀ α)
    η α = return {α}
    
    μ : (α : Obj C) → Hom C ([ [ F ]∘[ F ] ]₀ α) ([ F ]₀ α)
    μ α = join {α}
    
    naturalη : {α β : Obj C} {f : Hom C α β} 
             → [ F ]₁ f ∘C η α ≡ η β ∘C [ Id[ C ] ]₁ f
    naturalη {α} {β} {f} = fun-ext $ λ (x : α) → begin
      fmap f (return x)
        ≡⟨ law-monad-fmap f (return x) ⟩
      return x >>= (return ∘C f)
        ≡⟨ law-left-id x (return ∘C f) ⟩
      return (f x) ∎
    
    NatTrans-η : NatTrans Id[ C ] F
    NatTrans-η = naturalTransformation η naturalη

    naturalμ : {α β : Obj C} {f : Hom C α β}
             → [ F ]₁ f ∘C μ α ≡ μ β ∘C [ [ F ]∘[ F ] ]₁ f
    naturalμ {α} {β} {f} = fun-ext $ λ (mma : M (M α)) → begin 
      fmap f (join mma)
        ≡⟨ refl ⟩
      fmap f (mma >>= idF)
        ≡⟨ law-monad-fmap f (mma >>= idF) ⟩
      (mma >>= idF) >>= (return ∘C f)
        ≡⟨ sym $ law-assoc mma idF (return ∘C f) ⟩
      mma >>= (λ ma → ma >>= (return ∘C f))
        ≡⟨ cong (λ X → mma >>= X) (fun-ext $ λ ma → sym $ law-left-id (ma >>= (return ∘C f)) idF) ⟩
      mma >>= (λ ma → return (ma >>= (return ∘C f)) >>= idF)
        ≡⟨ law-assoc mma (λ ma → return (ma >>= (return ∘C f))) idF ⟩
      (mma >>= (λ ma → return (ma >>= (return ∘C f)))) >>= idF
        ≡⟨ cong (λ X → (mma >>= X) >>= idF) (fun-ext $ λ ma → cong (λ X → return X) (sym $ law-monad-fmap f ma)) ⟩
      (mma >>= (λ ma → return (fmap f ma))) >>= idF
        ≡⟨ refl ⟩
      (mma >>= (return ∘C (fmap f))) >>= idF
        ≡⟨ cong (λ X → X >>= idF) (sym $ law-monad-fmap (fmap f) mma) ⟩
      (fmap (fmap f) mma) >>= idF
        ≡⟨ refl ⟩
      join (fmap (fmap f) mma) ∎
    
    NatTrans-μ : NatTrans [ F ]∘[ F ] F
    NatTrans-μ = naturalTransformation μ naturalμ

    μCoher : {α : Obj C} 
           → μ α ∘C [ F ]₁ (μ α) ≡ μ α ∘C μ ([ F ]₀ α)
    μCoher {α} = fun-ext $ λ (mma : M (M (M α))) → begin
      join (fmap (join {α}) mma)
        ≡⟨ refl ⟩
      fmap (join {α}) mma >>= idF
        ≡⟨ cong (λ X → X >>= idF) (law-monad-fmap (join {α}) mma) ⟩
      (mma >>= (λ ma → return (join {α} ma))) >>= idF
        ≡⟨ refl ⟩
      (mma >>= (λ ma → return (ma >>= idF))) >>= idF
        ≡⟨ sym $ law-assoc mma (λ x → return (x >>= idF)) idF ⟩
      mma >>= (λ ma → return (ma >>= idF) >>= idF)
        ≡⟨ cong (λ X → mma >>= X) (fun-ext $ λ ma → law-left-id (ma >>= idF) idF) ⟩
      mma >>= (λ ma → ma >>= idF)
        ≡⟨ law-assoc mma idF idF ⟩
      (mma >>= idF) >>= idF
        ≡⟨ refl ⟩
      join {α} (join {M α} mma) ∎
    
    ηCoherL : {α : Obj C} 
            → μ α ∘C [ F ]₁ (η α) ≡ NatTrans.η Id⟨ F ⟩ α
    ηCoherL {α} = fun-ext $ λ (ma : M α) → begin
      join {α} (fmap (return {α}) ma)
        ≡⟨ refl ⟩
      fmap (return {α}) ma >>= idF
        ≡⟨ cong (λ X → X >>= idF) (law-monad-fmap (return {α}) ma) ⟩
      (ma >>= (return ∘C return)) >>= idF
        ≡⟨ sym $ law-assoc ma (return ∘C return) idF ⟩
      ma >>= (λ a → return (return a) >>= idF)
        ≡⟨ cong (λ X → ma >>= X) (fun-ext $ λ a → law-left-id (return a) idF) ⟩
      ma >>= return
        ≡⟨ law-right-id ma ⟩
      ma ∎
    
    ηCoherR : {α : Obj C} 
            → μ α ∘C η ([ F ]₀ α) ≡ NatTrans.η Id⟨ F ⟩ α
    ηCoherR {α} = fun-ext $ λ (ma : M α) → begin
      join {α} (return {M α} ma)
        ≡⟨ refl ⟩
      return {M α} ma >>= idF
        ≡⟨ law-left-id ma idF ⟩
      ma ∎
