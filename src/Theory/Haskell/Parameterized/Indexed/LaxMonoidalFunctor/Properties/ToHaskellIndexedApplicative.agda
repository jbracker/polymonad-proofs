
open import Level
open import Function renaming ( _∘_ to _∘F_ ; id to idF )

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality renaming ( refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ; cong₂ to hcong₂ )
open ≡-Reasoning

open import Extensionality

open import Haskell
open import Haskell.Functor hiding ( functor ) renaming ( Functor to HaskellFunctor )
open import Haskell.Applicative using ( _***_ )
open import Haskell.Parameterized.Indexed.Applicative

open import Theory.Category.Definition
open import Theory.Category.Examples.SetCat renaming ( setCategory to SetCat )
open import Theory.Category.Examples.Codiscrete renaming ( codiscreteCategory to Codisc )
open import Theory.Category.Monoidal
open import Theory.Category.Monoidal.Examples.SetCat renaming ( setMonoidalCategory to SetMonCat )
open import Theory.Functor.Definition hiding ( functor )
open import Theory.Functor.Composition
open import Theory.Functor.Monoidal
open import Theory.Functor.Properties.IsomorphicHaskellFunctor
open import Theory.Natural.Transformation

open import Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor

module Theory.Haskell.Parameterized.Indexed.LaxMonoidalFunctor.Properties.ToHaskellIndexedApplicative where

-- open Category hiding ( Obj ; Hom )
open MonoidalCategory hiding ( id )

IndexedLaxMonoidalFunctor→HaskellIndexedApplicative
  : {ℓIxs : Level} {Ixs : Set ℓIxs} 
  → (IndexedLaxMonoidalFunctor (Codisc Ixs) (SetMonCat {zero}) (SetMonCat {zero}))
  → (Σ (Ixs → Ixs → TyCon) (IxApplicative Ixs))
IndexedLaxMonoidalFunctor→HaskellIndexedApplicative {ℓIxs} {Ixs} FMon = F' , indexed-applicative pure _<*>_ HaskFunc law-id law-composition law-homomorphism law-interchange law-applicative-fmap
  where
    SetCat' = SetCat {zero}
    SetMonCat' = SetMonCat {zero}
    
    I = Codisc Ixs
    
    open IndexedLaxMonoidalFunctor FMon renaming ( μ-natural-transformation to monNatTrans )
    open NaturalTransformation renaming ( η to nat-η )
    
    F' : Ixs → Ixs → TyCon
    F' i j α = [ F (codisc i j) ]₀ α
    
    fmap : {i j : Ixs} {α β : Type} → (α → β) → F' i j α → F' i j β
    fmap {i} {j} {α} {β} f Fα = Functor.F₁ (F (codisc i j)) f Fα
    
    unit' : {i : Ixs} → F' i i (Lift ⊤)
    unit' {i} = ε i (lift tt)
    
    pure : {i : Ixs} {α : Type} → α → F' i i α
    pure {i} {α} a = fmap (λ _ → a) unit'
    
    _**_ : {i j k : Ixs} {α β : Type} → F' i j α → F' j k β → F' i k (α × β)
    _**_ {i} {j} {k} {α} {β} Fα Fβ = μ (codisc i j) (codisc j k) α β (Fα , Fβ)
    
    _<*>_ : {i j k : Ixs} {α β : Type} → F' i j (α → β) → F' j k α → F' i k β
    _<*>_ {i} {j} {k} {α} {β} Fα→β Fα = fmap (λ {(f , a) → f a}) (Fα→β ** Fα)
    
    HaskFunc : (i j : Ixs) → HaskellFunctor (F' i j)
    HaskFunc i j = Functor→HaskellFunctor (F (codisc i j))
    
    abstract
      nat : {i j k : Ixs} {a b : Category.Obj (SetCat' ×C SetCat')}
          → {f : Category.Hom (SetCat' ×C SetCat') a b}
          → (fmap (proj₁ f *** proj₂ f)) ∘F (nat-η (monNatTrans (codisc i j) (codisc j k)) a)
          ≡ (nat-η (monNatTrans (codisc i j) (codisc j k)) b) ∘F (fmap (proj₁ f) *** fmap (proj₂ f))
      nat {i} {j} {k} {a} {b} {f} = natural (monNatTrans (codisc i j) (codisc j k)) {a} {b} {f}
    
    abstract
      law-naturality : {i j k : Ixs} {α β γ δ : Type} → (f : α → β) (g : γ → δ) (u : F' i j α) (v : F' j k γ) 
                     → fmap (f *** g) (u ** v) ≡ fmap f u ** fmap g v
      law-naturality {i} {j} {k} {α} {β} {γ} {δ} f g u v = begin
        ( fmap (f *** g) ∘F (nat-η (monNatTrans (codisc i j) (codisc j k)) (α , γ)) ) (u , v)
          ≡⟨ cong (λ X → X (u , v)) (nat {f = (f , g)}) ⟩
        nat-η (monNatTrans (codisc i j) (codisc j k)) (β , δ) (fmap f u , fmap g v) ∎
    
    abstract
      law-left-identity' : {i j : Ixs} {α : Type} → (v : F' i j α) 
                         → fmap proj₂ (unit' ** v) ≡ v
      law-left-identity' {i} {j} {α} v = begin
        (fmap proj₂ ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x)) ) (lift tt , v) 
          ≡⟨ cong (λ X → X (lift tt , v)) (sym (≅-to-≡ $ left-unitality α)) ⟩
        proj₂ {a = zero} (lift tt , v) 
          ≡⟨⟩
        v ∎
    
    abstract
      law-left-identity : {i j : Ixs} {α : Type} → (v : F' i j α) 
                        → (unit' ** v) ≡ fmap (λ a → (lift tt , a)) v
      law-left-identity {i} {j} {α} v = begin
        (nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (λ X → (X ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)) (sym (Functor.id (F (codisc i j)))) ⟩
        (fmap (λ x → x) ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)
          ≡⟨ refl ⟩
        (fmap ((λ a → (lift tt , a)) ∘F proj₂) ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (λ X → (X ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)) (Functor.compose (F (codisc i j))) ⟩
        (fmap (λ a → (lift tt , a)) ∘F fmap proj₂ ∘F nat-η (monNatTrans (codisc i i) (codisc i j)) (Lift ⊤ , α) ∘F (ε i *** (λ x → x))) (lift tt , v)
          ≡⟨ cong (fmap (λ a → (lift tt , a))) (law-left-identity' v) ⟩
        fmap (λ a → (lift tt , a)) v ∎
    
    abstract
      law-right-identity' : {i j : Ixs} {α : Type} → (v : F' i j α) 
                          → fmap proj₁ (v ** unit') ≡ v
      law-right-identity' {i} {j} {α} v = cong (λ X → X (v , lift tt)) (sym (≅-to-≡ $ right-unitality α))
    
    abstract
      law-right-identity : {i j : Ixs} {α : Type} → (v : F' i j α) 
                         → (v ** unit') ≡ fmap (λ a → (a , lift tt)) v
      law-right-identity {i} {j} {α} v = begin
        (nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)
          ≡⟨ cong (λ X → (X ∘F nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)) (sym $ Functor.id (F (codisc i j))) ⟩
        (fmap (λ x → x) ∘F nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)
          ≡⟨ refl ⟩
        (fmap ((λ a → (a , lift tt)) ∘F proj₁) ∘F nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)
          ≡⟨ cong (λ X → (X ∘F nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)) (Functor.compose (F (codisc i j))) ⟩
        (fmap (λ a → (a , lift tt)) ∘F fmap proj₁ ∘F nat-η (monNatTrans (codisc i j) (codisc j j)) (α , Lift ⊤) ∘F ((λ x → x) *** ε j)) (v , lift tt)
          ≡⟨ cong (fmap (λ a → (a , lift tt))) (law-right-identity' v) ⟩
        fmap (λ a → (a , lift tt)) v ∎
    
    abstract
      law-applicative-fmap : {i j : Ixs} {α β : Type} 
                           → (f : α → β) → (x : F' i j α) 
                           → fmap f x ≡ pure f <*> x
      law-applicative-fmap {i} {j} {α} {β} f x = begin
        fmap f x 
          ≡⟨ refl ⟩
        fmap ((λ x → f (proj₂ {a = zero} x)) ∘F (λ a → (lift tt , a))) x
          ≡⟨ cong (λ X → X x) (Functor.compose (F (codisc i j))) ⟩
        fmap (λ x → f (proj₂ x)) (fmap (λ a → (lift tt , a)) x)
          ≡⟨ cong (fmap (λ x₁ → f (proj₂ x₁))) (sym $ law-left-identity x) ⟩
        fmap (λ x → f (proj₂ x)) (unit' ** x)
          ≡⟨ refl ⟩
        fmap ( (λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ x → x)) ) (ε i (lift tt) ** x)
          ≡⟨ cong (λ X → X (ε i (lift tt) ** x)) (Functor.compose (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ x → x)) (ε i (lift tt) ** x))
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a }) X) (law-naturality (λ _ → f) (λ z → z) (ε i (lift tt)) x) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε i (lift tt))) ** fmap (λ x → x) x)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε i (lift tt))) ** X)) (cong (λ X → X x) (Functor.id (F (codisc i j)))) ⟩
        fmap (λ {(f , a) → f a}) ((fmap (λ _ → f) (ε i (lift tt))) ** x) ∎
    
    abstract
      law-id : {i j : Ixs} {α : Type} 
             → (v : F' i j α) 
             → (pure (λ x → x) <*> v) ≡ v
      law-id {i} {j} {α} v = begin
        (pure (λ x → x) <*> v)
          ≡⟨ sym $ law-applicative-fmap (λ x → x) v ⟩
        fmap (λ x → x) v
          ≡⟨ cong (λ X → X v) (Functor.id (F (codisc i j))) ⟩
        v ∎
    
    abstract
      law-associativity : {α β γ : Type} {i j k l : Ixs} → (u : F' i j α) (v : F' j k β) (w : F' k l γ) 
                        → fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) ≡ u ** (v ** w)
      law-associativity {α} {β} {γ} {i} {j} {k} {l} u v w = sym $ begin
        (nat-η (monNatTrans (codisc i j) (codisc j l)) (α , (β × γ)) ∘F (idF *** nat-η (monNatTrans (codisc j k) (codisc k l)) (β , γ))) (u , (v , w)) 
          ≡⟨ cong (λ X → X ((u , v) , w)) (sym $ ≅-to-≡ $ assoc FMon α β γ) ⟩
        (fmap (λ {((a , b) , c) → (a , (b , c))}) ∘F nat-η (monNatTrans (codisc i k) (codisc k l)) ((α × β) , γ) ∘F (nat-η (monNatTrans (codisc i j) (codisc j k)) (α , β) *** idF)) ((u , v) , w) ∎
    
    abstract
      law-composition : {α β γ : Type} {i j k l : Ixs} 
                      → (u : F' i j (β → γ)) (v : F' j k (α → β)) (w : F' k l α)
                      → (((pure _∘′_ <*> u) <*> v) <*> w) ≡ (u <*> (v <*> w))
      law-composition {α} {β} {γ} {i} {j} {k} {l} u v w = begin
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** u)) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** X u)) ** v) ** w)) (sym $ Functor.id (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap (λ _ → _∘′_) unit' ** fmap idF u)) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) (fmap (λ { (f , a) → f a }) X ** v) ** w))
                  (sym $ law-naturality (λ _ → _∘′_) idF unit' u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) (unit' ** u))) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) X)) ** v) ** w) ) 
                  (law-left-identity u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap (λ {(f , a) → f a}) (fmap ((λ _ → _∘′_) *** idF) (fmap (λ a → (lift tt , a)) u))) ** v) ** w) 
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X (fmap (λ a → (lift tt , a)) u)) ** v) ** w)) (sym $ Functor.compose (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap ((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** idF)) (fmap (λ a → (lift tt , a)) u)) ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((X u) ** v) ** w)) (sym $ Functor.compose (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** X v) ** w)) (sym $ Functor.id (F (codisc j k))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) ((fmap g u) ** fmap idF v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) X ** w)) (sym $ law-naturality g idF u v) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ {(f , a) → f a}) (fmap (g *** idF) (u ** v)) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (X (u ** v) ** w)) (sym $ Functor.compose (F (codisc i k))) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** w)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** X w)) (sym $ Functor.id (F (codisc k l))) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ {(f , a) → f a}) ∘F (g *** idF)) (u ** v) ** fmap idF w)
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality ((λ {(f , a) → f a}) ∘F (g *** idF)) idF (u ** v) w) ⟩
        fmap (λ {(f , a) → f a}) (fmap (((λ {(f , a) → f a}) ∘F (g *** idF)) *** idF) ((u ** v) ** w))
          ≡⟨ cong (λ X → X ((u ** v) ** w)) (sym $ Functor.compose (F (codisc i l))) ⟩
        fmap h ((u ** v) ** w)
          ≡⟨ refl ⟩
        fmap (h' ∘F (λ {((a , b) , c) → (a , (b , c))})) ( (u ** v) ** w )
          ≡⟨ cong (λ X → X ( (u ** v) ** w )) (Functor.compose (F (codisc i l))) ⟩
        fmap h' (fmap (λ {((a , b) , c) → (a , (b , c))}) ( (u ** v) ** w ) )
          ≡⟨ cong (fmap h') (law-associativity u v w) ⟩
        fmap h' (u ** (v ** w))
          ≡⟨ cong (λ X → X (u ** (v ** w))) (Functor.compose (F (codisc i l))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (idF *** (λ {(f , a) → f a})) (u ** (v ** w)))
          ≡⟨ cong (fmap (λ { (f , a) → f a })) (law-naturality idF (λ {(f , a) → f a}) u (v ** w)) ⟩
        fmap (λ {(f , a) → f a}) (fmap idF u ** fmap (λ {(f , a) → f a}) (v ** w))
          ≡⟨ cong (λ X → fmap (λ { (f , a) → f a }) (X u ** fmap (λ { (f , a) → f a }) (v ** w))) (Functor.id (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (u ** fmap (λ {(f , a) → f a}) (v ** w)) ∎
        where
          g = (((λ {(f , a) → f a}) ∘F ((λ _ → _∘′_) *** idF)) ∘F (λ a → (lift tt , a)))
          h = ((λ {(f , a) → f a}) ∘F (((λ {(f , a) → f a}) ∘F (g *** idF)) *** idF))
          h' = ((λ {(f , a) → f a}) ∘F (idF *** (λ {(f , a) → f a})))
    
    abstract
      law-homomorphism : {i : Ixs} {α β : Type} 
                       → (x : α) → (f : α → β) 
                       → pure {i} f <*> pure {i} x ≡ pure {i} (f x)
      law-homomorphism {i} {α} {β} x f = begin
        fmap (λ {(f , a) → f a}) (fmap (λ _ → f) unit' ** fmap (λ _ → x) unit')
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality (λ _ → f) (λ _ → x) unit' unit') ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → f) *** (λ _ → x)) (unit' ** unit'))
          ≡⟨ cong (λ X → X (unit' ** unit')) (sym $ Functor.compose (F (codisc i i))) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (unit' ** unit')
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x)))) (law-left-identity unit') ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → f) *** (λ _ → x))) (fmap (λ a → (lift tt , a)) unit')
          ≡⟨ cong (λ X → X unit') (sym $ Functor.compose (F (codisc i i))) ⟩
        fmap (λ _ → f x) unit' ∎
    
    abstract
      law-interchange : {i j : Ixs} {α β : Type} 
                      → (u : F' i j (α → β)) → (x : α) 
                      → u <*> pure {j} x ≡ pure {i} (λ f → f x) <*> u
      law-interchange {i} {j} {α} {β} u x = begin
        fmap (λ {(f , a) → f a}) (u ** fmap (λ _ → x) unit')
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (X u ** fmap (λ _ → x) unit')) (sym $ Functor.id (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap idF u ** fmap (λ _ → x) unit')
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (sym $ law-naturality idF (λ _ → x) u unit') ⟩
        fmap (λ {(f , a) → f a}) (fmap (idF *** (λ _ → x)) (u ** unit'))
          ≡⟨ cong (λ X → X (u ** unit')) (sym $ Functor.compose (F (codisc i j))) ⟩
        fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x))) (u ** unit')
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x)))) (law-right-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F (idF *** (λ _ → x))) (fmap (λ a → (a , lift tt)) u)
          ≡⟨ cong (λ X → X u) (sym $ Functor.compose (F (codisc i j))) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF) ∘F (λ a → (lift tt , a))) u
          ≡⟨ cong (λ X → X u) (Functor.compose (F (codisc i j))) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF)) (fmap (λ a → (lift tt , a)) u)
          ≡⟨ cong (fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF))) (sym $ law-left-identity u) ⟩
        fmap ((λ {(f , a) → f a}) ∘F ((λ _ → (λ f → f x)) *** idF)) (unit' ** u)
          ≡⟨ cong (λ X → X (unit' ** u)) (Functor.compose (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap ((λ _ → (λ f → f x)) *** idF) (unit' ** u))
          ≡⟨ cong (fmap (λ {(f , a) → f a})) (law-naturality (λ _ f → f x) idF unit' u) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** fmap idF u)
          ≡⟨ cong (λ X → fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** X u)) (Functor.id (F (codisc i j))) ⟩
        fmap (λ {(f , a) → f a}) (fmap (λ _ → (λ f → f x)) unit' ** u) ∎

