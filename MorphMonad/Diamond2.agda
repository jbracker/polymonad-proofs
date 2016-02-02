 
module MorphMonad.Diamond2 where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Identity
open import Polymonad
open import Monad.Polymonad

open import MorphMonad.Types

lawDiamond2 : ∀ (M N R T : MonadMorphTyCons)
            → (∃ λ(S : MonadMorphTyCons) → Morph[ N , R ]▷ S × Morph[ M , S ]▷ T)
            → (∃ λ(P : MonadMorphTyCons) → Morph[ M , N ]▷ P × Morph[ P , R ]▷ T)
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , () , IdentB)
lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b3 , ())
lawDiamond2 (inj₁ IdentTC) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b3 , ())
lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₁ IdentTC) (inj₁ IdentTC , b3 , ())
lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₁ IdentTC) (inj₁ IdentTC , b3 , ())
lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b3 , ())
lawDiamond2 (inj₂ (inj₁ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b3 , ())
lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b3 , ())
lawDiamond2 (inj₂ (inj₂ MonadTC)) N R (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b3 , ())
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , Morph2I1B) = inj₂ (inj₁ MonadTC) , Morph2I1B , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , Morph1I2B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph1I2B
lawDiamond2 M (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ T) (inj₁ IdentTC , () , b4)
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , ApplyB) = inj₁ IdentTC , IdentB , MorphI21B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , FunctorB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , FunctorB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph121B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , MonadB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph121B
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MorphI12B) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MorphI12B) = inj₁ IdentTC , IdentB , MorphI12B
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , MorphI12B) = inj₁ IdentTC , IdentB , ApplyB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MorphI12B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph1I2B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , MorphI12B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph1I2B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MorphI12B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , MorphI12B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph122B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , MorphI12B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , MorphI12B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph122B
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , MorphI21B) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , MorphI21B) = inj₁ IdentTC , IdentB , ApplyB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , MorphI21B) = inj₁ IdentTC , IdentB , MorphI21B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , MorphI21B) = inj₂ (inj₁ MonadTC) , ApplyB , FunctorB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , MorphI21B) = inj₂ (inj₁ MonadTC) , MorphI21B , FunctorB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , MorphI21B) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , MorphI21B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph121B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , MorphI21B) = inj₂ (inj₁ MonadTC) , MorphI21B , MonadB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , MorphI21B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph121B
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , ApplyB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , ApplyB) = inj₁ IdentTC , IdentB , MorphI12B
lawDiamond2 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , ApplyB) = inj₁ IdentTC , IdentB , ApplyB
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph1I2B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph1I2B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph122B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B
lawDiamond2 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , FunctorB , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , MonadB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph2I1B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph221B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph221B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph112B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph112B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph121B) = inj₂ (inj₁ MonadTC) , FunctorB , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph121B) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph121B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph121B) = inj₂ (inj₁ MonadTC) , MonadB , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , FunctorB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph121B) = inj₂ (inj₁ MonadTC) , MonadB , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph121B) = inj₂ (inj₁ MonadTC) , MonadB , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , MonadB
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph2I1B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph211B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , FunctorB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph211B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph121B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , MonadB
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph121B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph122B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph1I2B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph122B) = inj₂ (inj₁ MonadTC) , MonadB , Morph122B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph112B
lawDiamond2 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , MonadB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , Morph1I2B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , Morph122B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , Morph112B
lawDiamond2 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , Morph122B
