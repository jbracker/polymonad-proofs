
open import Level
open import Function renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning

open import Equality
open import Extensionality
open import Bijection hiding ( refl ; sym ; trans )
open import Haskell hiding ( Hask )
open import Haskell.Functor renaming ( Functor to HaskellFunctor ; functor-eq to hask-functor-eq ) hiding ( functor )
open import Haskell.Parameterized.Indexed.Monad renaming ( indexed-monad-eq to hask-indexed-monad-eq )
open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Functor.Definition
open import Theory.Functor.Composition
open import Theory.Natural.Transformation
open import Theory.Haskell.Parameterized.Indexed.Monad
open import Theory.Haskell.Parameterized.Indexed.Monad.Equality
open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.FromHaskellIndexedMonad
open import Theory.Haskell.Parameterized.Indexed.Monad.Properties.ToHaskellIndexedMonad

module Theory.Haskell.Parameterized.Indexed.Monad.Properties.IsomorphicHaskellIndexedMonad where

private
  SetCat' = setCategory {zero}

open Category renaming ( id to cat-id )

HaskellIndexedMonad↔IndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                 → (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
                                 ↔ (Σ ({i j : Ixs} → Hom (Codisc Ixs) i j → Functor SetCat' SetCat') (IndexedMonad (Codisc Ixs)))
HaskellIndexedMonad↔IndexedMonad {ℓIxs} {Ixs} = bijection HaskellIndexedMonad→IndexedMonad IndexedMonad→HaskellIndexedMonad l→r→l r→l→r
  where
    open NaturalTransformation renaming ( η to nat-η )
    
    I = Codisc Ixs
    _∘I_ = _∘_ I
    
    abstract
      l→r→l : (b : Σ ({i j : Ixs} → Hom I i j → Functor SetCat' SetCat') (IndexedMonad I)) 
            → HaskellIndexedMonad→IndexedMonad (IndexedMonad→HaskellIndexedMonad b) ≡ b
      l→r→l (F , monad) = Σ-eq' (implicit-fun-ext $ λ (i : Ixs) → implicit-fun-ext $ λ (j : Ixs) → fun-ext $ λ { (codisc .i .j) → refl }) 
                        $ λ F'≡F → het-indexed-monad-eq F'≡F ( het-fun-ext (het-fun-ext hrefl $ λ (i : Ixs) → hrefl) 
                                                             $ λ (i : Ixs) → het-natural-transformation-eq refl refl hrefl)
                        $ het-implicit-fun-ext (het-fun-ext hrefl $ λ (i : Ixs) → hcong (λ X → {j k : Ixs} 
                                                                                             → (f : CodiscreteArrow i j) → (g : CodiscreteArrow j k) 
                                                                                             → NaturalTransformation [ X g ]∘[ X f ] (X (g ∘I f))) 
                                                                                        (≡-to-≅ F'≡F)) 
                        $ λ (i : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (j : Ixs) → hcong (λ X → {k : Ixs} 
                                                                                                           → (f : CodiscreteArrow i j) → (g : CodiscreteArrow j k) 
                                                                                                           → NaturalTransformation [ X g ]∘[ X f ] (X (g ∘I f))) 
                                                                                                      (≡-to-≅ F'≡F)) 
                        $ λ (j : Ixs) → het-implicit-fun-ext (het-fun-ext hrefl $ λ (k : Ixs) → hcong (λ X → (f : CodiscreteArrow i j) → (g : CodiscreteArrow j k) 
                                                                                                           → NaturalTransformation [ X g ]∘[ X f ] (X (g ∘I f))) 
                                                                                                      (≡-to-≅ F'≡F)) 
                        $ λ (k : Ixs) → het-fun-ext (het-fun-ext hrefl $ λ { (codisc .i .j) → hcong (λ X → (g : CodiscreteArrow j k) 
                                                                                                         → NaturalTransformation [ X g ]∘[ X (codisc i j) ] (X (g ∘I codisc i j)) ) 
                                                                                                    (≡-to-≅ F'≡F) })
                        $ λ { (codisc .i .j) → het-fun-ext (het-fun-ext hrefl $ λ { (codisc .j .k) → hrefl }) 
                        $ λ { (codisc .j .k) → ≡-to-≅ 
                        $ natural-transformation-eq $ fun-ext 
                        $ λ (α : Type) → cong (λ X → nat-η (μ (codisc i j) (codisc j k)) α ∘F X) (Functor.id (F (codisc j k))) } }  
        where 
          open IndexedMonad monad
          b' = HaskellIndexedMonad→IndexedMonad (IndexedMonad→HaskellIndexedMonad (F , monad))
          monad' = proj₂ b'
          F' = proj₁ b'
      
    abstract
      r→l→r : (a : Σ (Ixs → Ixs → TyCon) (IxMonad Ixs)) 
            → IndexedMonad→HaskellIndexedMonad (HaskellIndexedMonad→IndexedMonad a) ≡ a
      r→l→r (M , monad) = Σ-eq refl $ ≡-to-≅ 
                        $ hask-indexed-monad-eq bind-eq (implicit-fun-ext $ λ α → implicit-fun-ext $ λ i → refl) 
                        $ fun-ext $ λ i → fun-ext $ λ j → hask-functor-eq refl
        where
          _>>=₁_ = IxMonad._>>=_ (proj₂ (IndexedMonad→HaskellIndexedMonad (HaskellIndexedMonad→IndexedMonad (M , monad))))
          _>>=₀_ = IxMonad._>>=_ monad
          
          open IxMonad monad          
          abstract
            bind-eq : (λ {α β} {i j k} → _>>=₁_ {α} {β} {i} {j} {k}) ≡ _>>=₀_
            bind-eq = implicit-fun-ext $ λ α → implicit-fun-ext $ λ β → implicit-fun-ext $ λ i → implicit-fun-ext $ λ j → implicit-fun-ext $ λ k → fun-ext $ λ ma → fun-ext $ λ f → begin
              ((fmap f ma) >>= (λ x → x)) 
                ≡⟨ cong (λ X → X >>= id) (sym (law-monad-fmap f ma)) ⟩
              ((ma >>= (return ∘F f)) >>= id) 
                ≡⟨ sym (law-assoc ma (return ∘F f) id) ⟩
              (ma >>= (λ x → return (f x) >>= id)) 
                ≡⟨ cong (λ X → ma >>= X) (fun-ext (λ x → law-right-id (f x) id)) ⟩
              (ma >>= f) ∎
    
IndexedMonad↔HaskellIndexedMonad : {ℓIxs : Level} {Ixs : Set ℓIxs} 
                                 → (Σ ({i j : Ixs} → Hom (Codisc Ixs) i j → Functor SetCat' SetCat') (IndexedMonad (Codisc Ixs)))
                                 ↔ (Σ (Ixs → Ixs → TyCon) (IxMonad Ixs))
IndexedMonad↔HaskellIndexedMonad = Bijection.sym HaskellIndexedMonad↔IndexedMonad
