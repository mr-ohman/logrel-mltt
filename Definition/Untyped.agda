{-# OPTIONS --without-K --safe #-}

module Definition.Untyped where

open import Flex.Untyped renaming (Term to Term′; Subst to Subst′) public

open import Tools.Product
open import Tools.Nat
open import Tools.Fin
open import Tools.List
import Tools.PropositionalEquality as PE

infix 30 Π_▹_
infixr 22 _▹▹_
infix 30 Σ_▹_
infixr 22 _××_
infix 30 ⟦_⟧_▹_


private
  variable
    n m ℓ : Nat


data defKind′ : Set where
  Ukind Pikind Lamkind Appkind Sigmakind Prodkind Fstkind Sndkind Natkind Zerokind Suckind Natreckind Unitkind Starkind Emptykind Emptyreckind : defKind′


defKindArgs : defKind′ → List KindArg
defKindArgs Ukind = []
defKindArgs Pikind = b0 ∷ b1 ∷ []
defKindArgs Lamkind = b1 ∷ []
defKindArgs Appkind = ne0 ∷ b0 ∷ []
defKindArgs Sigmakind = b0 ∷ b1 ∷ []
defKindArgs Prodkind = b0 ∷ b0 ∷ []
defKindArgs Fstkind = ne0 ∷ []
defKindArgs Sndkind = ne0 ∷ []
defKindArgs Natkind = []
defKindArgs Zerokind = []
defKindArgs Suckind = b0 ∷ []
defKindArgs Natreckind = b1 ∷ b0 ∷ b0 ∷ ne0 ∷ []
defKindArgs Unitkind = []
defKindArgs Starkind = []
defKindArgs Emptykind = []
defKindArgs Emptyreckind = b0 ∷ ne0 ∷ []

defKind : DynKind
defKind = dynKind defKind′ defKindArgs

Term : Nat → Set
Term = Term′ defKind

Subst : Nat → Nat → Set
Subst = Subst′ defKind

private
  variable
    A F H t u v : Term n
    B E G       : Term (1+ n)

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U      : Term n                      -- Universe.
U = gen Ukind []

Π_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent function type (B is a binder).
Π A ▹ B = gen Pikind (A ∷ B ∷ [])

Σ_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent sum type (B is a binder).
Σ A ▹ B = gen Sigmakind (A ∷ B ∷ [])

ℕ      : Term n                      -- Type of natural numbers.
ℕ = gen Natkind []

Empty : Term n                       -- Empty type
Empty = gen Emptykind []

Unit  : Term n                       -- Unit type
Unit = gen Unitkind []

lam    : (t : Term (1+ n)) → Term n  -- Function abstraction (binder).
lam t = gen Lamkind (t ∷ [])

_∘_    : (t u : Term n) → Term n     -- Application.
t ∘ u = gen Appkind (t ∷ u ∷ [])


prod : (t u : Term n) → Term n       -- Dependent products
prod t u = gen Prodkind (t ∷ u ∷ [])

fst : (t : Term n) → Term n          -- First projection
fst t = gen Fstkind (t ∷ [])

snd : (t : Term n) → Term n          -- Second projection
snd t = gen Sndkind (t ∷ [])

-- Introduction and elimination of natural numbers.
zero   : Term n                      -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term n)       → Term n -- Successor.
suc t = gen Suckind (t ∷ [])

natrec : (A : Term (1+ n)) (t u v : Term n) → Term n  -- Natural number recursor (A is a binder).
natrec A t u v = gen Natreckind (A ∷ t ∷ u ∷ v ∷ [])


star : Term n                        -- Unit element
star = gen Starkind []

Emptyrec : (A e : Term n) → Term n   -- Empty type recursor
Emptyrec A e = gen Emptyreckind (A ∷ e ∷ [])

-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BΠ ⟧ F ▹ G = Π F ▹ G
⟦ BΣ ⟧ F ▹ G = Σ F ▹ G

-- data Neutral : Term n → Set where
--   var       : (x : Fin n) → Neutral (var x)
--   ∘ₙ        : Neutral t   → Neutral (t ∘ u)
--   fstₙ      : Neutral t   → Neutral (fst t)
--   sndₙ      : Neutral t   → Neutral (snd t)
--   natrecₙ   : Neutral v   → Neutral (natrec G t u v)
--   Emptyrecₙ : Neutral t   → Neutral (Emptyrec A t)

pattern ∘ₙ neT = gen Appkind {_ ∷ _ ∷ []} _ (here neT)
pattern ∘⊥ = gen Appkind {_ ∷ _ ∷ []} _ (there (there ()))
pattern fstₙ neT = gen Fstkind {_ ∷ []} _ (here neT)
pattern sndₙ neT = gen Sndkind {_ ∷ []} _ (here neT)
pattern natrecₙ neV = gen Natreckind {_ ∷ _ ∷ _ ∷ _ ∷ []} _ (there (there (there (here neV))))
pattern Emptyrecₙ neT = gen Emptyreckind {_ ∷ _ ∷ []} _ (there (here neT))

pattern ∘ₙf t u = gen Appkind {_ ∷ _ ∷ []} _ (t ne∷ u nf∷ [])
pattern ∘⊥f = gen Appkind {_ ∷ _ ∷ []} _ (_ nf∷ _ nf∷ ())
pattern fstₙf t = gen Fstkind {_ ∷ []} _ (t ne∷ [])
pattern sndₙf t = gen Sndkind {_ ∷ []} _ (t ne∷ [])
pattern natrecₙf G t u v = gen Natreckind {_ ∷ _ ∷ _ ∷ _ ∷ []} _ (G nf∷ t nf∷ u nf∷ v ne∷ [])
pattern Emptyrecₙf A t = gen Emptyreckind {_ ∷ _ ∷ []} _ (A nf∷ t ne∷ [])


-- data Whnf {n : Nat} : Term n → Set where

--   -- Type constructors are whnfs.
--   Uₙ     : Whnf U
--   Πₙ     : Whnf (Π A ▹ B)
--   Σₙ     : Whnf (Σ A ▹ B)
--   ℕₙ     : Whnf ℕ
--   Unitₙ  : Whnf Unit
--   Emptyₙ : Whnf Empty

--   -- Introductions are whnfs.
--   lamₙ  : Whnf (lam t)
--   zeroₙ : Whnf zero
--   sucₙ  : Whnf (suc t)
--   starₙ : Whnf star
--   prodₙ : Whnf (prod t u)

--   -- Neutrals are whnfs.
--   ne    : Neutral t → Whnf t

pattern Uₙ = cons (cons Ukind {[]} _)
pattern Πₙ = cons (cons Pikind {_ ∷ _ ∷ []} _)
pattern Σₙ = cons (cons Sigmakind {_ ∷ _ ∷ []} _)
pattern ℕₙ = cons (cons Natkind {[]} _)
pattern Unitₙ = cons (cons Unitkind {[]} _)
pattern Emptyₙ = cons (cons Emptykind {[]} _)
pattern lamₙ = cons (cons Lamkind {_ ∷ []} _)
pattern zeroₙ = cons (cons Zerokind {[]} _)
pattern sucₙ = cons (cons Suckind {_ ∷ []} _)
pattern starₙ = cons (cons Starkind {[]} _)
pattern prodₙ = cons (cons Prodkind {_ ∷ _ ∷ []} _)

pattern Uₙf = cons (cons Ukind {[]} _ [])
pattern Πₙf F G = cons (cons Pikind {_ ∷ _ ∷ []} _ (F nf∷ G nf∷ []))
pattern Σₙf F G = cons (cons Sigmakind {_ ∷ _ ∷ []} _ (F nf∷ G nf∷ []))
pattern ℕₙf = cons (cons Natkind {[]} _ [])
pattern Unitₙf = cons (cons Unitkind {[]} _ [])
pattern Emptyₙf = cons (cons Emptykind {[]} _ [])
pattern lamₙf t = cons (cons Lamkind {_ ∷ []} _ (t nf∷ []))
pattern zeroₙf = cons (cons Zerokind {[]} _ [])
pattern sucₙf t = cons (cons Suckind {_ ∷ []} _ (t nf∷ []))
pattern starₙf = cons (cons Starkind {[]} _ [])
pattern prodₙf t u = cons (cons Prodkind {_ ∷ _ ∷ []} _ (t nf∷ u nf∷ []))


U≢ne : Neutral A → U PE.≢ A
U≢ne = cons≢ne (cons Ukind _)

ℕ≢ne : Neutral A → ℕ PE.≢ A
ℕ≢ne = cons≢ne (cons Natkind _)

Empty≢ne : Neutral A → Empty PE.≢ A
Empty≢ne = cons≢ne (cons Emptykind _)

Unit≢ne : Neutral A → Unit PE.≢ A
Unit≢ne = cons≢ne (cons Unitkind _)

B≢ne : ∀ W → Neutral A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne BΠ = cons≢ne (cons Pikind _)
B≢ne BΣ = cons≢ne (cons Sigmakind _)

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne = cons≢ne (cons Zerokind _)

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne = cons≢ne (cons Suckind _)

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} : Term n → Set where
  zeroₙ′ :             Natural zero
  sucₙ′  :             Natural (suc t)
  ne    : Neutral t → Natural t


-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {n : Nat} : Term n → Set where
  Πₙ′     :             Type (Π A ▹ B)
  Σₙ′     :             Type (Σ A ▹ B)
  ℕₙ′     :             Type ℕ
  Emptyₙ′ :             Type Empty
  Unitₙ′  :             Type Unit
  ne     : Neutral t → Type t

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ′
⟦ BΣ ⟧-type = Σₙ′

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {n : Nat} : Term n → Set where
  lamₙ′ : Function (lam t)
  ne   : Neutral t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {n : Nat} : Term n → Set where
  prodₙ′ : Product (prod t u)
  ne    : Neutral t → Product t

-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

naturalWhnf : Natural t → Whnf t
naturalWhnf sucₙ′   = sucₙ
naturalWhnf zeroₙ′  = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Πₙ′     = Πₙ
typeWhnf Σₙ′     = Σₙ
typeWhnf ℕₙ′     = ℕₙ
typeWhnf Emptyₙ′ = Emptyₙ
typeWhnf Unitₙ′  = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf lamₙ′   = lamₙ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodₙ′  = prodₙ
productWhnf (ne x) = ne x

⟦_⟧ₙ : (W : BindingType) → Whnf (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ BΠ = Πₙ
⟦_⟧ₙ BΣ = Σₙ

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n} (wk ρ t)
wkNatural ρ sucₙ′   = sucₙ′
wkNatural ρ zeroₙ′  = zeroₙ′
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n} (wk ρ t)
wkType ρ Πₙ′     = Πₙ′
wkType ρ Σₙ′     = Σₙ′
wkType ρ ℕₙ′     = ℕₙ′
wkType ρ Emptyₙ′ = Emptyₙ′
wkType ρ Unitₙ′  = Unitₙ′
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n} (wk ρ t)
wkFunction ρ lamₙ′   = lamₙ′
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n} (wk ρ t)
wkProduct ρ prodₙ′  = prodₙ′
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W F G = W H E  then  F = H  and  G = E.

B-PE-injectivity : ∀ W → ⟦ W ⟧ F ▹ G PE.≡ ⟦ W ⟧ H ▹ E → F PE.≡ H × G PE.≡ E
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : suc t PE.≡ suc u → t PE.≡ u
suc-PE-injectivity PE.refl = PE.refl

-- Non-dependent version of Π.

_▹▹_ : Term n → Term n → Term n
A ▹▹ B = Π A ▹ wk1 B

-- Non-dependent products.

_××_ : Term n → Term n → Term n
A ×× B = Σ A ▹ wk1 B

B-subst : (σ : Subst m n) (W : BindingType) (F : Term n) (G : Term (1+ n))
        → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ BΠ F G = PE.refl
B-subst σ BΣ F G = PE.refl
