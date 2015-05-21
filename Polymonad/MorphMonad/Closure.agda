 
module Polymonad.MorphMonad.Closure where

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

open import Polymonad.MorphMonad.Types

lawClosure : ∀ (M N P S T U : MonadMorphTyCons)
           → ( Morph[ M , N ]▷ P × Morph[ S , idTC ]▷ M × Morph[ T , idTC ]▷ N × Morph[ P , idTC ]▷ U )
           → Morph[ S , T ]▷ U
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (IdentB , IdentB , IdentB , IdentB) = IdentB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (IdentB , IdentB , IdentB , ReturnB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (IdentB , IdentB , IdentB , ReturnB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) U (IdentB , () , IdentB , b4)
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) U (IdentB , () , IdentB , b4)
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) S (inj₂ (inj₁ MonadTC)) U (IdentB , b2 , () , b4)
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₁ IdentTC) S (inj₂ (inj₂ MonadTC)) U (IdentB , b2 , () , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) S T U (() , b2 , b3 , b4)
lawClosure M N (inj₂ (inj₁ MonadTC)) S T (inj₁ IdentTC) (b1 , b2 , b3 , ())
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (ReturnB , IdentB , IdentB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , ReturnB , IdentB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , ReturnB , IdentB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph2I1B , ReturnB , IdentB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph2I1B , ReturnB , IdentB , Morph1I2B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ReturnB , () , IdentB , b4)
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ReturnB , () , IdentB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , FunctorB , IdentB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph2I1B , Morph1I2B , IdentB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph2I1B , Morph1I2B , IdentB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , Morph2I1B , IdentB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , Morph2I1B , IdentB , Morph1I2B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph2I1B , FunctorB , IdentB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph2I1B , FunctorB , IdentB , Morph1I2B) = FunctorB
lawClosure M (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) S (inj₂ (inj₁ MonadTC)) (inj₂ U) (b1 , b2 , () , b4)
lawClosure M (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) S (inj₂ (inj₂ MonadTC)) (inj₂ U) (b1 , b2 , () , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph211B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph211B , ReturnB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ApplyB , () , ReturnB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ApplyB , () , ReturnB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , ReturnB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , Morph2I1B , ReturnB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , Morph2I1B , ReturnB , Morph1I2B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph211B , Morph1I2B , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph211B , Morph1I2B , ReturnB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph211B , FunctorB , ReturnB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph211B , FunctorB , ReturnB , Morph1I2B) = FunctorB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MorphI21B , IdentB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MorphI21B , IdentB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph121B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph121B , ReturnB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph221B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph221B , ReturnB , ReturnB , Morph1I2B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (MorphI21B , () , ReturnB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (MorphI21B , () , ReturnB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph121B , FunctorB , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph121B , FunctorB , ReturnB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph121B , Morph2I1B , ReturnB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph121B , Morph2I1B , ReturnB , Morph1I2B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph221B , Morph1I2B , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph221B , Morph1I2B , ReturnB , Morph1I2B) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph221B , FunctorB , ReturnB , FunctorB) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph221B , FunctorB , ReturnB , Morph1I2B) = FunctorB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , FunctorB , Morph1I2B) = MorphI12B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , FunctorB , Morph1I2B) = MorphI12B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , ReturnB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , ReturnB , FunctorB , Morph1I2B) = MorphI12B
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (ApplyB , () , FunctorB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (ApplyB , () , FunctorB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , FunctorB , FunctorB) = MonadB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , FunctorB , Morph1I2B) = Morph112B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , Morph2I1B , FunctorB , FunctorB) = Morph211B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , Morph2I1B , FunctorB , Morph1I2B) = Morph212B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , Morph1I2B , FunctorB , FunctorB) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , Morph1I2B , FunctorB , Morph1I2B) = Morph112B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , FunctorB , FunctorB , FunctorB) = Morph211B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , FunctorB , FunctorB , Morph1I2B) = Morph212B
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , Morph2I1B , FunctorB) = MorphI21B
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , Morph2I1B , Morph1I2B) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , Morph2I1B , FunctorB) = MorphI21B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , Morph2I1B , Morph1I2B) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , ReturnB , Morph2I1B , FunctorB) = MorphI21B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , ReturnB , Morph2I1B , Morph1I2B) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (ApplyB , () , Morph2I1B , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (ApplyB , () , Morph2I1B , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , Morph2I1B , FunctorB) = Morph121B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , Morph2I1B , Morph1I2B) = Morph122B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , Morph2I1B , Morph2I1B , FunctorB) = Morph221B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , Morph2I1B , Morph2I1B , Morph1I2B) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , Morph1I2B , Morph2I1B , FunctorB) = Morph121B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , Morph1I2B , Morph2I1B , Morph1I2B) = Morph122B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph211B , FunctorB , Morph2I1B , FunctorB) = Morph221B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph211B , FunctorB , Morph2I1B , Morph1I2B) = MonadB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MorphI21B , IdentB , Morph1I2B , FunctorB) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MorphI21B , IdentB , Morph1I2B , Morph1I2B) = MorphI12B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , ReturnB , Morph1I2B , FunctorB) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , ReturnB , Morph1I2B , Morph1I2B) = MorphI12B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , ReturnB , Morph1I2B , FunctorB) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , ReturnB , Morph1I2B , Morph1I2B) = MorphI12B
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (MorphI21B , () , Morph1I2B , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (MorphI21B , () , Morph1I2B , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , FunctorB , Morph1I2B , FunctorB) = MonadB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , FunctorB , Morph1I2B , Morph1I2B) = Morph112B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , Morph2I1B , Morph1I2B , FunctorB) = Morph211B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , Morph2I1B , Morph1I2B , Morph1I2B) = Morph212B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , Morph1I2B , Morph1I2B , FunctorB) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , Morph1I2B , Morph1I2B , Morph1I2B) = Morph112B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , FunctorB , Morph1I2B , FunctorB) = Morph211B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , FunctorB , Morph1I2B , Morph1I2B) = Morph212B
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MorphI21B , IdentB , FunctorB , FunctorB) = MorphI21B
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MorphI21B , IdentB , FunctorB , Morph1I2B) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , ReturnB , FunctorB , FunctorB) = MorphI21B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , ReturnB , FunctorB , Morph1I2B) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , ReturnB , FunctorB , FunctorB) = MorphI21B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , ReturnB , FunctorB , Morph1I2B) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (MorphI21B , () , FunctorB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (MorphI21B , () , FunctorB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , FunctorB , FunctorB , FunctorB) = Morph121B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , FunctorB , FunctorB , Morph1I2B) = Morph122B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph121B , Morph2I1B , FunctorB , FunctorB) = Morph221B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph121B , Morph2I1B , FunctorB , Morph1I2B) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , Morph1I2B , FunctorB , FunctorB) = Morph121B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , Morph1I2B , FunctorB , Morph1I2B) = Morph122B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph221B , FunctorB , FunctorB , FunctorB) = Morph221B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph221B , FunctorB , FunctorB , Morph1I2B) = MonadB
lawClosure M (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) S (inj₁ IdentTC) (inj₁ IdentTC) (b1 , b2 , IdentB , ())
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (ReturnB , IdentB , IdentB , Morph2I1B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (ReturnB , IdentB , IdentB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ReturnB , () , IdentB , b4)
lawClosure (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ReturnB , () , IdentB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph1I2B , ReturnB , IdentB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph1I2B , ReturnB , IdentB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , ReturnB , IdentB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , ReturnB , IdentB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph1I2B , FunctorB , IdentB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph1I2B , FunctorB , IdentB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph1I2B , Morph2I1B , IdentB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph1I2B , Morph2I1B , IdentB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , Morph1I2B , IdentB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , Morph1I2B , IdentB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (FunctorB , FunctorB , IdentB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (FunctorB , FunctorB , IdentB , FunctorB) = FunctorB
lawClosure M (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₁ MonadTC)) U (b1 , b2 , () , b4)
lawClosure M (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₂ MonadTC)) U (b1 , b2 , () , b4)
lawClosure M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₁ IdentTC) (inj₁ IdentTC) (b1 , b2 , ReturnB , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MorphI12B , IdentB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MorphI12B , IdentB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (MorphI12B , () , ReturnB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (MorphI12B , () , ReturnB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph112B , ReturnB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph112B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph212B , ReturnB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph212B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph112B , FunctorB , ReturnB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph112B , FunctorB , ReturnB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph112B , Morph2I1B , ReturnB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph112B , Morph2I1B , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph212B , Morph1I2B , ReturnB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph212B , Morph1I2B , ReturnB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph212B , FunctorB , ReturnB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph212B , FunctorB , ReturnB , FunctorB) = FunctorB
lawClosure M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₁ IdentTC) (inj₁ IdentTC) (b1 , b2 , ReturnB , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ApplyB , () , ReturnB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ U) (ApplyB , () , ReturnB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph122B , ReturnB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph122B , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , ReturnB , Morph2I1B) = ReturnB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , ReturnB , FunctorB) = ReturnB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph122B , FunctorB , ReturnB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph122B , FunctorB , ReturnB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (Morph122B , Morph2I1B , ReturnB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (Morph122B , Morph2I1B , ReturnB , FunctorB) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , Morph1I2B , ReturnB , Morph2I1B) = FunctorB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , Morph1I2B , ReturnB , FunctorB) = Morph1I2B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , ReturnB , Morph2I1B) = Morph2I1B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , ReturnB , FunctorB) = FunctorB
lawClosure M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (b1 , b2 , FunctorB , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MorphI12B , IdentB , FunctorB , Morph2I1B) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MorphI12B , IdentB , FunctorB , FunctorB) = MorphI12B
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (MorphI12B , () , FunctorB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (MorphI12B , () , FunctorB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , ReturnB , FunctorB , Morph2I1B) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , ReturnB , FunctorB , FunctorB) = MorphI12B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , ReturnB , FunctorB , Morph2I1B) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , ReturnB , FunctorB , FunctorB) = MorphI12B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , FunctorB , FunctorB , Morph2I1B) = MonadB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , FunctorB , FunctorB , FunctorB) = Morph112B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , Morph2I1B , FunctorB , Morph2I1B) = Morph211B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , Morph2I1B , FunctorB , FunctorB) = Morph212B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , Morph1I2B , FunctorB , Morph2I1B) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , Morph1I2B , FunctorB , FunctorB) = Morph112B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , FunctorB , FunctorB , Morph2I1B) = Morph211B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , FunctorB , FunctorB , FunctorB) = Morph212B
lawClosure M (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (b1 , b2 , Morph2I1B , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MorphI12B , IdentB , Morph2I1B , Morph2I1B) = MorphI21B
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MorphI12B , IdentB , Morph2I1B , FunctorB) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (MorphI12B , () , Morph2I1B , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (MorphI12B , () , Morph2I1B , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , ReturnB , Morph2I1B , Morph2I1B) = MorphI21B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , ReturnB , Morph2I1B , FunctorB) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , ReturnB , Morph2I1B , Morph2I1B) = MorphI21B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , ReturnB , Morph2I1B , FunctorB) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , FunctorB , Morph2I1B , Morph2I1B) = Morph121B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , FunctorB , Morph2I1B , FunctorB) = Morph122B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph112B , Morph2I1B , Morph2I1B , Morph2I1B) = Morph221B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph112B , Morph2I1B , Morph2I1B , FunctorB) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , Morph1I2B , Morph2I1B , Morph2I1B) = Morph121B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , Morph1I2B , Morph2I1B , FunctorB) = Morph122B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph212B , FunctorB , Morph2I1B , Morph2I1B) = Morph221B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph212B , FunctorB , Morph2I1B , FunctorB) = MonadB
lawClosure M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₁ MonadTC)) (inj₁ IdentTC) (b1 , b2 , Morph1I2B , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , Morph1I2B , Morph2I1B) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , Morph1I2B , FunctorB) = MorphI12B
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (ApplyB , () , Morph1I2B , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ U) (ApplyB , () , Morph1I2B , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , ReturnB , Morph1I2B , Morph2I1B) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , ReturnB , Morph1I2B , FunctorB) = MorphI12B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , Morph1I2B , Morph2I1B) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , Morph1I2B , FunctorB) = MorphI12B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , FunctorB , Morph1I2B , Morph2I1B) = MonadB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , FunctorB , Morph1I2B , FunctorB) = Morph112B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , Morph2I1B , Morph1I2B , Morph2I1B) = Morph211B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , Morph2I1B , Morph1I2B , FunctorB) = Morph212B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , Morph1I2B , Morph1I2B , Morph2I1B) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , Morph1I2B , Morph1I2B , FunctorB) = Morph112B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , Morph1I2B , Morph2I1B) = Morph211B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , Morph1I2B , FunctorB) = Morph212B
lawClosure M (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) S (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (b1 , b2 , FunctorB , ())
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (ApplyB , IdentB , FunctorB , Morph2I1B) = MorphI21B
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (ApplyB , IdentB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (ApplyB , () , FunctorB , b4)
lawClosure (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ U) (ApplyB , () , FunctorB , b4)
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , ReturnB , FunctorB , Morph2I1B) = MorphI21B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , ReturnB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , ReturnB , FunctorB , Morph2I1B) = MorphI21B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₁ IdentTC) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , ReturnB , FunctorB , FunctorB) = ApplyB
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , FunctorB , FunctorB , Morph2I1B) = Morph121B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , FunctorB , FunctorB , FunctorB) = Morph122B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , Morph1I2B , FunctorB , Morph2I1B) = Morph121B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , Morph1I2B , FunctorB , FunctorB) = Morph122B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (Morph122B , Morph2I1B , FunctorB , Morph2I1B) = Morph221B
lawClosure (inj₂ (inj₁ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (Morph122B , Morph2I1B , FunctorB , FunctorB) = MonadB
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₁ MonadTC)) (MonadB , FunctorB , FunctorB , Morph2I1B) = Morph221B
lawClosure (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (inj₂ (inj₂ MonadTC)) (MonadB , FunctorB , FunctorB , FunctorB) = MonadB
