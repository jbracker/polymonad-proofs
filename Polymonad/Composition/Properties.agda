 
module Polymonad.Composition.Properties where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad
open import Identity
open import Polymonad.Identity
open import Polymonad.Composable
open import Polymonad.Composition
open import Polymonad.Composition.Composable


composition→¬[M₁,N]▷M₂
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {cpm₁ : ComposablePolymonad pm₁}
  → {cpm₂ : ComposablePolymonad pm₂}
  → (cpm : ComposablePolymonad (polymonadCompose cpm₁ cpm₂))
  → {M₁ : TyCons₁} {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₂ : TyCons₂} 
  → ¬ ( B[ (inj₂ (inj₁ M₁)) , N ] (polymonadCompose cpm₁ cpm₂) ▷ (inj₂ (inj₂ M₂)) )
composition→¬[M₁,N]▷M₂ cpm {N = inj₁ IdentTC} ()
composition→¬[M₁,N]▷M₂ cpm {N = inj₂ (inj₁ N₁)} ()
composition→¬[M₁,N]▷M₂ cpm {N = inj₂ (inj₂ N₂)} ()

composition→¬[N,M₁]▷M₂
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {cpm₁ : ComposablePolymonad pm₁}
  → {cpm₂ : ComposablePolymonad pm₂}
  → (cpm : ComposablePolymonad (polymonadCompose cpm₁ cpm₂))
  → {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₁ : TyCons₁} {M₂ : TyCons₂} 
  → ¬ ( B[ N , (inj₂ (inj₁ M₁)) ] (polymonadCompose cpm₁ cpm₂) ▷ (inj₂ (inj₂ M₂)) )
composition→¬[N,M₁]▷M₂ cpm {N = inj₁ IdentTC} ()
composition→¬[N,M₁]▷M₂ cpm {N = inj₂ (inj₁ N₁)} ()
composition→¬[N,M₁]▷M₂ cpm {N = inj₂ (inj₂ N₂)} ()

composition→¬[M₂,N]▷M₁
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {cpm₁ : ComposablePolymonad pm₁}
  → {cpm₂ : ComposablePolymonad pm₂}
  → (cpm : ComposablePolymonad (polymonadCompose cpm₁ cpm₂))
  → {M₂ : TyCons₂} {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₁ : TyCons₁} 
  → ¬ ( B[ (inj₂ (inj₂ M₂)) , N ] (polymonadCompose cpm₁ cpm₂) ▷ (inj₂ (inj₁ M₁)) )
composition→¬[M₂,N]▷M₁ cpm {N = inj₁ IdentTC} ()
composition→¬[M₂,N]▷M₁ cpm {N = inj₂ (inj₁ N₁)} ()
composition→¬[M₂,N]▷M₁ cpm {N = inj₂ (inj₂ N₂)} ()

composition→¬[N,M₂]▷M₁
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {cpm₁ : ComposablePolymonad pm₁}
  → {cpm₂ : ComposablePolymonad pm₂}
  → (cpm : ComposablePolymonad (polymonadCompose cpm₁ cpm₂))
  → {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₂ : TyCons₂} {M₁ : TyCons₁}
  → ¬ ( B[ N , (inj₂ (inj₂ M₂)) ] (polymonadCompose cpm₁ cpm₂) ▷ (inj₂ (inj₁ M₁)) )
composition→¬[N,M₂]▷M₁ cpm {N = inj₁ IdentTC} ()
composition→¬[N,M₂]▷M₁ cpm {N = inj₂ (inj₁ N₁)} ()
composition→¬[N,M₂]▷M₁ cpm {N = inj₂ (inj₂ N₂)} ()
