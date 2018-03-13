
module Hicks.Equality where

-- Stdlib
open import Level renaming ( suc to lsuc ; zero to lzero )
open import Function hiding ( id ) renaming ( _∘_ to _∘F_ )

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; cong₂ to hcong₂ ; proof-irrelevance to het-proof-irrelevance )

-- Local
open import Haskell
open import Identity
open import Equality
open import Extensionality
open import Congruence
open import Hicks.Polymonad

-------------------------------------------------------------------------------
-- Definition of 2-Functors
-------------------------------------------------------------------------------

abstract
  hicks-polymonad-eq : {ℓ : Level} {TyCons : Set ℓ} {Id : TyCons}
               → {B[_,_]▷₁_ : (M N P : TyCons) → Set ℓ}
               → {B[_,_]▷₂_ : (M N P : TyCons) → Set ℓ}
               → {⟨_⟩₁ : TyCons → TyCon}
               → {⟨_⟩₂ : TyCons → TyCon}
               → {bind₁ : {M N P : TyCons} → B[ M , N ]▷₁ P → [ ⟨ M ⟩₁ , ⟨ N ⟩₁ ]▷ ⟨ P ⟩₁}
               → {bind₂ : {M N P : TyCons} → B[ M , N ]▷₂ P → [ ⟨ M ⟩₂ , ⟨ N ⟩₂ ]▷ ⟨ P ⟩₂}
               → {law-id₁ : ⟨ Id ⟩₁ ≡ Identity}
               → {law-id₂ : ⟨ Id ⟩₂ ≡ Identity}
               → {lawFunctor₁ : ∀ (M : TyCons) → ∃ λ(b : B[ M , Id ]▷₁ M) 
                              → ∀ {α : Type} (m : ⟨ M ⟩₁ α) → (bind₁ b) m (id law-id₁) ≡ m}
               → {lawFunctor₂ : ∀ (M : TyCons) → ∃ λ(b : B[ M , Id ]▷₂ M) 
                              → ∀ {α : Type} (m : ⟨ M ⟩₂ α) → (bind₂ b) m (id law-id₂) ≡ m}
               → {lawMorph1₁ : ∀ (M N : TyCons) 
                            → (B[ M , Id ]▷₁ N → B[ Id , M ]▷₁ N)}
               → {lawMorph1₂ : ∀ (M N : TyCons) 
                            → (B[ M , Id ]▷₂ N → B[ Id , M ]▷₂ N)}
               → {lawMorph2₁ : ∀ (M N : TyCons) 
                            → (B[ Id , M ]▷₁ N → B[ M , Id ]▷₁ N)}
               → {lawMorph2₂ : ∀ (M N : TyCons) 
                            → (B[ Id , M ]▷₂ N → B[ M , Id ]▷₂ N)}
               → {lawMorph3₁ : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷₁ N) (b₂ : B[ Id , M ]▷₁ N)
                            → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩₁ β) 
                            → (bind₁ b₁) (f v) (id law-id₁) ≡ (bind₁ b₂) ((id law-id₁) v) f}
               → {lawMorph3₂ : ∀ (M N : TyCons) (b₁ : B[ M , Id ]▷₂ N) (b₂ : B[ Id , M ]▷₂ N)
                            → ∀ {α β : Type} (v : α) (f : α → ⟨ M ⟩₂ β) 
                            → (bind₂ b₁) (f v) (id law-id₂) ≡ (bind₂ b₂) ((id law-id₂) v) f}
               → {lawDiamond1₁ : ∀ (M N R T : TyCons)
                               → (∃ λ(P : TyCons) → B[ M , N ]▷₁ P × B[ P , R ]▷₁ T)
                               → (∃ λ(S : TyCons) → B[ N , R ]▷₁ S × B[ M , S ]▷₁ T)}
               → {lawDiamond1₂ : ∀ (M N R T : TyCons)
                               → (∃ λ(P : TyCons) → B[ M , N ]▷₂ P × B[ P , R ]▷₂ T)
                               → (∃ λ(S : TyCons) → B[ N , R ]▷₂ S × B[ M , S ]▷₂ T)}
               → {lawDiamond2₁ : ∀ (M N R T : TyCons)
                               → (∃ λ(S : TyCons) → B[ N , R ]▷₁ S × B[ M , S ]▷₁ T)
                               → (∃ λ(P : TyCons) → B[ M , N ]▷₁ P × B[ P , R ]▷₁ T)}
               → {lawDiamond2₂ : ∀ (M N R T : TyCons)
                               → (∃ λ(S : TyCons) → B[ N , R ]▷₂ S × B[ M , S ]▷₂ T)
                               → (∃ λ(P : TyCons) → B[ M , N ]▷₂ P × B[ P , R ]▷₂ T)}
               → {law-assoc₁ : ∀ (M N P R T S : TyCons) 
                             → (b₁ : B[ M , N ]▷₁ P) → (b₂ : B[ P , R ]▷₁ T) 
                             → (b₃ : B[ N , R ]▷₁ S) → (b₄ : B[ M , S ]▷₁ T)
                             → ∀ {α β γ : Type} (m : ⟨ M ⟩₁ α) (f : α → ⟨ N ⟩₁ β) (g : β → ⟨ R ⟩₁ γ)
                             → (bind₁ b₂) ((bind₁ b₁) m f) g ≡ (bind₁ b₄) m (λ x → (bind₁ b₃) (f x) g)}
               → {law-assoc₂ : ∀ (M N P R T S : TyCons) 
                             → (b₁ : B[ M , N ]▷₂ P) → (b₂ : B[ P , R ]▷₂ T) 
                             → (b₃ : B[ N , R ]▷₂ S) → (b₄ : B[ M , S ]▷₂ T)
                             → ∀ {α β γ : Type} (m : ⟨ M ⟩₂ α) (f : α → ⟨ N ⟩₂ β) (g : β → ⟨ R ⟩₂ γ)
                             → (bind₂ b₂) ((bind₂ b₁) m f) g ≡ (bind₂ b₄) m (λ x → (bind₂ b₃) (f x) g)}
               → {lawClosure₁ : ∀ (M N P S T U : TyCons)
                              → ( B[ M , N ]▷₁ P × B[ S , Id ]▷₁ M × B[ T , Id ]▷₁ N × B[ P , Id ]▷₁ U )
                              → B[ S , T ]▷₁ U}
               → {lawClosure₂ : ∀ (M N P S T U : TyCons)
                              → ( B[ M , N ]▷₂ P × B[ S , Id ]▷₂ M × B[ T , Id ]▷₂ N × B[ P , Id ]▷₂ U )
                              → B[ S , T ]▷₂ U}
               → (eqBT : B[_,_]▷₁_ ≡ B[_,_]▷₂_)
               → (eqTC : ⟨_⟩₁ ≡ ⟨_⟩₂)
               → (eqB : (λ {M N P} b {α β} → bind₁ {M} {N} {P} b {α} {β}) ≅ (λ {M N P} b {α β} → bind₂ {M} {N} {P} b {α} {β}))
               → (eqId : law-id₁ ≅ law-id₂)
               → (eqFun : (λ M → lawFunctor₁ M) ≅ (λ M → lawFunctor₂ M))
               → (eqMor1 : (λ M N b → lawMorph1₁ M N b) ≅ lawMorph1₂)
               → (eqMor2 : (λ M N b → lawMorph2₁ M N b) ≅ lawMorph2₂)
               → (eqDia1 : (λ M N R T b → lawDiamond1₁ M N R T b) ≅ lawDiamond1₂)
               → (eqDia2 : (λ M N R T b → lawDiamond2₁ M N R T b) ≅ lawDiamond2₂)
               → (eqClo : (λ M N P S T U b → lawClosure₁ M N P S T U b) ≅ lawClosure₂)
               → hicksPolymonad {l = ℓ} {TyCons = TyCons} {Id = Id} B[_,_]▷₁_ ⟨_⟩₁ bind₁ law-id₁ lawFunctor₁ lawMorph1₁ lawMorph2₁ lawMorph3₁ lawDiamond1₁ lawDiamond2₁ law-assoc₁ lawClosure₁ 
               ≡ hicksPolymonad {l = ℓ} {TyCons = TyCons} {Id = Id} B[_,_]▷₂_ ⟨_⟩₂ bind₂ law-id₂ lawFunctor₂ lawMorph1₂ lawMorph2₂ lawMorph3₂ lawDiamond1₂ lawDiamond2₂ law-assoc₂ lawClosure₂ 
  hicks-polymonad-eq {ℓ} {TyCons} {Id} {B[_,_]▷_} {.B[_,_]▷_} {⟨_⟩} {.⟨_⟩} {b} {.b} 
               {lid} {.lid} {fun} {.fun} {mor1} {.mor1} {mor2} {.mor2} {mor3₁} {mor3₂} {dia1} {.dia1} {dia2} {.dia2} {ass₁} {ass₂} {clo} {.clo} 
               refl refl hrefl hrefl hrefl hrefl hrefl hrefl hrefl hrefl
    = cong₂ (λ mor3 ass → hicksPolymonad {l = ℓ} {TyCons = TyCons} {Id = Id} (B[_,_]▷_) (⟨_⟩) b lid fun mor1 mor2 mor3 dia1 dia2 ass clo) p2 p3
    where
      abstract
        p2 : (λ M N b1 b2 {α β} v f → mor3₁ M N b1 b2 {α} {β} v f) ≡ (λ M N b1 b2 {α β} v f → mor3₂ M N b1 b2 {α} {β} v f)
        p2 = fun-ext 
           $ λ M → fun-ext 
           $ λ N → fun-ext 
           $ λ b1 → fun-ext 
           $ λ b2 → implicit-fun-ext 
           $ λ α → implicit-fun-ext 
           $ λ β → fun-ext 
           $ λ v → fun-ext 
           $ λ f → proof-irrelevance (mor3₁ M N b1 b2 {α} {β} v f) (mor3₂ M N b1 b2 {α} {β} v f)
        
        p3 : (λ M N P R T S b1 b2 b3 b4 {α β γ} m f g → ass₁ M N P R T S b1 b2 b3 b4 {α} {β} {γ} m f g) ≡ (λ M N P R T S b1 b2 b3 b4 {α β γ} m f g → ass₂ M N P R T S b1 b2 b3 b4 {α} {β} {γ} m f g)
        p3 = fun-ext 
           $ λ M → fun-ext 
           $ λ N → fun-ext 
           $ λ P → fun-ext 
           $ λ R → fun-ext 
           $ λ T → fun-ext 
           $ λ S → fun-ext 
           $ λ b1 → fun-ext 
           $ λ b2 → fun-ext 
           $ λ b3 → fun-ext 
           $ λ b4 → implicit-fun-ext 
           $ λ α → implicit-fun-ext 
           $ λ β → implicit-fun-ext 
           $ λ γ → fun-ext 
           $ λ m → fun-ext 
           $ λ f → fun-ext 
           $ λ g → proof-irrelevance (ass₁ M N P R T S b1 b2 b3 b4 {α} {β} {γ} m f g) (ass₂ M N P R T S b1 b2 b3 b4 {α} {β} {γ} m f g)
 
