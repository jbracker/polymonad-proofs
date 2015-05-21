 
module Polymonad.MorphMonad.Diamond1 where

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
open import Polymonad.Composable
open import Polymonad.Principal
open import Monad
open import Monad.Polymonad
open import Monad.Composable
open import Monad.Principal

open import Polymonad.MorphMonad.Types

lawDiamond1 : ∀ (M N R T : MonadMorphTyCons)
            → (∃ λ(P : MonadMorphTyCons) → Morph[ M , N ]▷ P × Morph[ P , R ]▷ T)
            → (∃ λ(S : MonadMorphTyCons) → Morph[ N , R ]▷ S × Morph[ M , S ]▷ T)
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , IdentB) = inj₁ IdentTC , IdentB , IdentB
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC , IdentB , ())
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , ApplyB) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC , IdentB , MorphI21B) = inj₂ (inj₁ MonadTC) , MorphI21B , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ReturnB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , MorphI12B) = inj₂ (inj₁ MonadTC) , ApplyB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC , IdentB , ApplyB) = inj₂ (inj₁ MonadTC) , MorphI21B , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) R T (inj₁ IdentTC , () , b2)
lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b1 , ())
lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b1 , ())
lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC) , b1 , ())
lawDiamond1 M N (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b1 , ())
lawDiamond1 M N (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b1 , ())
lawDiamond1 M N (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC) , b1 , ())
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , FunctorB) = inj₁ IdentTC , IdentB , FunctorB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , FunctorB) = inj₁ IdentTC , IdentB , Morph2I1B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph1I2B) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph1I2B) = inj₂ (inj₁ MonadTC) , FunctorB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph1I2B) = inj₂ (inj₁ MonadTC) , Morph2I1B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph1I2B) = inj₁ IdentTC , IdentB , Morph1I2B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph1I2B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph1I2B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph1I2B) = inj₁ IdentTC , IdentB , FunctorB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph1I2B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph1I2B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph212B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB) = inj₂ (inj₁ MonadTC) , ApplyB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , MonadB) = inj₂ (inj₁ MonadTC) , MonadB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , MonadB) = inj₂ (inj₁ MonadTC) , Morph211B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph112B) = inj₂ (inj₁ MonadTC) , ApplyB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph211B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph112B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph112B) = inj₂ (inj₁ MonadTC) , MonadB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph112B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph212B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph121B) = inj₂ (inj₁ MonadTC) , MorphI21B , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph121B) = inj₂ (inj₁ MonadTC) , Morph221B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph121B) = inj₂ (inj₁ MonadTC) , MorphI21B , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph121B) = inj₂ (inj₁ MonadTC) , Morph221B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph121B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph121B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph121B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ReturnB , Morph122B) = inj₂ (inj₁ MonadTC) , MorphI21B , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , ApplyB , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MorphI21B , Morph122B) = inj₂ (inj₁ MonadTC) , Morph221B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , FunctorB , Morph122B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , MonadB , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph121B , Morph122B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph2I1B , Morph122B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph211B , Morph122B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC) , Morph221B , Morph122B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph212B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph2I1B) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph2I1B) = inj₂ (inj₁ MonadTC) , FunctorB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph2I1B) = inj₂ (inj₁ MonadTC) , Morph2I1B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph2I1B) = inj₁ IdentTC , IdentB , FunctorB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph2I1B) = inj₂ (inj₁ MonadTC) , FunctorB , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph2I1B) = inj₂ (inj₁ MonadTC) , Morph2I1B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph2I1B) = inj₁ IdentTC , IdentB , Morph2I1B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph2I1B) = inj₂ (inj₁ MonadTC) , FunctorB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph2I1B) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph211B) = inj₂ (inj₁ MonadTC) , ApplyB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph211B) = inj₂ (inj₁ MonadTC) , MonadB , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph211B) = inj₂ (inj₁ MonadTC) , ApplyB , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph211B) = inj₂ (inj₂ MonadTC) , Morph112B , Morph121B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph211B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph211B) = inj₂ (inj₁ MonadTC) , MonadB , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph211B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph221B) = inj₂ (inj₁ MonadTC) , MorphI21B , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph121B , ApplyB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , ApplyB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph221B) = inj₂ (inj₁ MonadTC) , MorphI21B , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph121B , MonadB
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , MonadB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph221B) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph221B) = inj₂ (inj₁ MonadTC) , Morph121B , Morph211B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph221B) = inj₂ (inj₁ MonadTC) , Morph221B , Morph211B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , FunctorB) = inj₁ IdentTC , IdentB , ReturnB
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , FunctorB) = inj₁ IdentTC , IdentB , Morph1I2B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , FunctorB) = inj₁ IdentTC , IdentB , FunctorB
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , FunctorB) = inj₂ (inj₁ MonadTC) , FunctorB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , FunctorB) = inj₂ (inj₁ MonadTC) , Morph2I1B , Morph212B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , Morph212B) = inj₂ (inj₁ MonadTC) , ApplyB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , Morph212B) = inj₂ (inj₁ MonadTC) , MonadB , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , Morph212B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , Morph212B) = inj₂ (inj₁ MonadTC) , MonadB , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , Morph212B) = inj₂ (inj₁ MonadTC) , ApplyB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , Morph212B) = inj₂ (inj₁ MonadTC) , MonadB , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , Morph212B) = inj₂ (inj₁ MonadTC) , Morph211B , Morph212B
lawDiamond1 (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ReturnB , MonadB) = inj₂ (inj₁ MonadTC) , MorphI21B , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MorphI12B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , MorphI12B
lawDiamond1 (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , ApplyB , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , MorphI12B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph1I2B , MonadB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph112B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , Morph112B
lawDiamond1 (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph122B , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , Morph112B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , FunctorB , MonadB) = inj₂ (inj₁ MonadTC) , MorphI21B , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , Morph212B , MonadB) = inj₂ (inj₁ MonadTC) , Morph121B , Morph212B
lawDiamond1 (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC) , MonadB , MonadB) = inj₂ (inj₁ MonadTC) , Morph221B , Morph212B

