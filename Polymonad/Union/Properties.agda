 
module Polymonad.Union.Properties where

-- Stdlib
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Local
open import Utilities
open import Haskell
open import Polymonad
open import Identity
open import Polymonad.Identity
open import Polymonad.Unionable
open import Polymonad.Union
open import Polymonad.Union.Unionable


union→¬[M₁,N]▷M₂
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {upm₁ : UnionablePolymonad pm₁}
  → {upm₂ : UnionablePolymonad pm₂}
  → (upm : UnionablePolymonad (polymonadUnion upm₁ upm₂))
  → {M₁ : TyCons₁} {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₂ : TyCons₂} 
  → ¬ ( B[ (inj₂ (inj₁ M₁)) , N ] (polymonadUnion upm₁ upm₂) ▷ (inj₂ (inj₂ M₂)) )
union→¬[M₁,N]▷M₂ upm {N = inj₁ IdentTC} ()
union→¬[M₁,N]▷M₂ upm {N = inj₂ (inj₁ N₁)} ()
union→¬[M₁,N]▷M₂ upm {N = inj₂ (inj₂ N₂)} ()

union→¬[N,M₁]▷M₂
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {upm₁ : UnionablePolymonad pm₁}
  → {upm₂ : UnionablePolymonad pm₂}
  → (upm : UnionablePolymonad (polymonadUnion upm₁ upm₂))
  → {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₁ : TyCons₁} {M₂ : TyCons₂} 
  → ¬ ( B[ N , (inj₂ (inj₁ M₁)) ] (polymonadUnion upm₁ upm₂) ▷ (inj₂ (inj₂ M₂)) )
union→¬[N,M₁]▷M₂ upm {N = inj₁ IdentTC} ()
union→¬[N,M₁]▷M₂ upm {N = inj₂ (inj₁ N₁)} ()
union→¬[N,M₁]▷M₂ upm {N = inj₂ (inj₂ N₂)} ()

union→¬[M₂,N]▷M₁
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {upm₁ : UnionablePolymonad pm₁}
  → {upm₂ : UnionablePolymonad pm₂}
  → (upm : UnionablePolymonad (polymonadUnion upm₁ upm₂))
  → {M₂ : TyCons₂} {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₁ : TyCons₁} 
  → ¬ ( B[ (inj₂ (inj₂ M₂)) , N ] (polymonadUnion upm₁ upm₂) ▷ (inj₂ (inj₁ M₁)) )
union→¬[M₂,N]▷M₁ upm {N = inj₁ IdentTC} ()
union→¬[M₂,N]▷M₁ upm {N = inj₂ (inj₁ N₁)} ()
union→¬[M₂,N]▷M₁ upm {N = inj₂ (inj₂ N₂)} ()

union→¬[N,M₂]▷M₁
  : ∀ {TyCons₁ TyCons₂ : Set}
  → {pm₁ : Polymonad (IdTyCons ⊎ TyCons₁) idTC}
  → {pm₂ : Polymonad (IdTyCons ⊎ TyCons₂) idTC}
  → {upm₁ : UnionablePolymonad pm₁}
  → {upm₂ : UnionablePolymonad pm₂}
  → (upm : UnionablePolymonad (polymonadUnion upm₁ upm₂))
  → {N : IdTyCons ⊎ (TyCons₁ ⊎ TyCons₂)} {M₂ : TyCons₂} {M₁ : TyCons₁}
  → ¬ ( B[ N , (inj₂ (inj₂ M₂)) ] (polymonadUnion upm₁ upm₂) ▷ (inj₂ (inj₁ M₁)) )
union→¬[N,M₂]▷M₁ upm {N = inj₁ IdentTC} ()
union→¬[N,M₂]▷M₁ upm {N = inj₂ (inj₁ N₁)} ()
union→¬[N,M₂]▷M₁ upm {N = inj₂ (inj₂ N₂)} ()
