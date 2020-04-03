-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.Untyped where

open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE


infixl 30 _∙_
infix 30 Π_▹_
infixr 22 _▹▹_
infix 30 Σ_▹_
infixr 22 _××_
infix 30 ⟦_⟧_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (snoc-lists, isomorphic to lists).

data Con (A : Set) : Set where
  ε   : Con A               -- Empty context.
  _∙_ : Con A → A → Con A  -- Context extension.

record GenT (A : Set) : Set where
  inductive
  constructor ⟦_,_⟧
  field
    l : Nat
    t : A

data Kind : Set where
  Ukind : Kind

  Pikind : Kind
  Lamkind : Kind
  Appkind : Kind

  Sigmakind : Kind
  Prodkind : Kind
  Fstkind : Kind
  Sndkind : Kind

  Natkind : Kind
  Zerokind : Kind
  Suckind : Kind
  Natreckind : Kind

  Unitkind : Kind
  Starkind : Kind

  Emptykind : Kind
  Emptyreckind : Kind

data Term : Set where
  var : (x : Nat) → Term
  gen : (k : Kind) (c : List (GenT Term)) → Term

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U      : Term                     -- Universe.
U = gen Ukind []

pattern Univ u = gen (Ukind u) []

Π_▹_   : (A B : Term)     → Term  -- Dependent function type (B is a binder).
Π A ▹ B = gen Pikind (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

Σ_▹_ : (A B : Term) → Term
Σ A ▹ B = gen Sigmakind (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

ℕ      : Term                     -- Type of natural numbers.
ℕ = gen Natkind []

Empty : Term
Empty = gen Emptykind []

Unit  : Term
Unit = gen Unitkind []

-- Lambda-calculus.
-- var    : (x : Nat)        → Term  -- Variable (de Bruijn index).
-- var = var

lam    : (t : Term)       → Term  -- Function abstraction (binder).
lam t = gen Lamkind (⟦ 1 , t ⟧ ∷ [])

_∘_    : (t u : Term)     → Term  -- Application.
t ∘ u = gen Appkind (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

-- Dependent products
prod : (t u : Term) → Term
prod t u = gen Prodkind (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ []) -- TODO (0, 0) since u doesn't have extra vars right?

fst : (t : Term) → Term
fst t = gen Fstkind (⟦ 0 , t ⟧ ∷ [])

snd : (t : Term) → Term
snd t = gen Sndkind (⟦ 0 , t ⟧ ∷ [])

-- Introduction and elimination of natural numbers.
zero   : Term                     -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term)       → Term  -- Successor.
suc t = gen Suckind (⟦ 0 , t ⟧ ∷ [])

natrec : (A t u v : Term) → Term  -- Recursor (A is a binder).
natrec A t u v = gen Natreckind (⟦ 1 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , v ⟧ ∷ [])

-- Unit type
star : Term
star = gen Starkind []

-- Empty type
Emptyrec : (A e : Term) → Term
Emptyrec A e = gen Emptyreckind (⟦ 0 , A ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

-- Binding types

data BindingType : Set where
  -- TODO these are horrible names, get mixed up with ΠB
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_▹_ : BindingType → Term → Term → Term
⟦ BΠ ⟧ F ▹ G = Π F ▹ G
⟦ BΣ ⟧ F ▹ G = Σ F ▹ G

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W F G = W H E  then  F = H  and  G = E.

B-PE-injectivity : ∀ {F G H E} W → ⟦ W ⟧ F ▹ G PE.≡ ⟦ W ⟧ H ▹ E → F PE.≡ H × G PE.≡ E
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : ∀ {n m} → suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term → Set where
  var       : ∀ n                     → Neutral (var n)
  ∘ₙ        : ∀ {k u}     → Neutral k → Neutral (k ∘ u)
  natrecₙ   : ∀ {C c g k} → Neutral k → Neutral (natrec C c g k)
  Emptyrecₙ : ∀ {A e}     → Neutral e → Neutral (Emptyrec A e)


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  Πₙ     : ∀ {A B} → Whnf (Π A ▹ B)
  Σₙ     : ∀ {A B} → Whnf (Σ A ▹ B)
  ℕₙ     : Whnf ℕ
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : ∀ {t} → Whnf (lam t)
  zeroₙ : Whnf zero
  sucₙ  : ∀ {t} → Whnf (suc t)
  starₙ : Whnf star
  prodₙ : ∀ {t u} → Whnf (prod t u)

  -- Neutrals are whnfs.
  ne    : ∀ {n} → Neutral n → Whnf n


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : ∀ {K} → Neutral K → U PE.≢ K
U≢ne () PE.refl

ℕ≢ne : ∀ {K} → Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

Empty≢ne : ∀ {K} → Neutral K → Empty PE.≢ K
Empty≢ne () PE.refl

Unit≢ne : ∀ {K} → Neutral K → Unit PE.≢ K
Unit≢ne () PE.refl

B≢ne : ∀ {F G K} W → Neutral K → ⟦ W ⟧ F ▹ G PE.≢ K
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

U≢B : ∀ {F G} W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ {F G} W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ {F G} W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ {F G} W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : ∀ {k} → Neutral k → zero PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → suc n PE.≢ k
suc≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural : Term → Set where
  zeroₙ :                     Natural zero
  sucₙ  : ∀ {t}             → Natural (suc t)
  ne    : ∀ {n} → Neutral n → Natural n

-- A whnf of type Unit is either star or neutral.

data Unitary : Term → Set where
  starₙ : Unitary star
  ne    : ∀ {s} → Neutral s → Unitary s

-- A (small) type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Πₙ : ∀ {A B} → Type (Π A ▹ B)
  Σₙ : ∀ {A B} → Type (Σ A ▹ B)
  ℕₙ : Type ℕ
  Emptyₙ : Type Empty
  Unitₙ : Type Unit
  ne : ∀{n} → Neutral n → Type n

⟦_⟧-type : ∀ (W : BindingType) {F} {G} → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function : Term → Set where
  lamₙ : ∀ {t} → Function (lam t)
  ne   : ∀ {n} → Neutral n → Function n

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product : Term → Set where
  prodₙ : ∀ {t u} → Product (prod t u)
  ne    : ∀ {n} → Neutral n → Product n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf sucₙ = sucₙ
naturalWhnf zeroₙ = zeroₙ
naturalWhnf (ne x) = ne x

unitaryWhnf : ∀ {s} → Unitary s → Whnf s
unitaryWhnf starₙ = starₙ
unitaryWhnf (ne x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Πₙ = Πₙ
typeWhnf Σₙ = Σₙ
typeWhnf ℕₙ = ℕₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {f} → Function f → Whnf f
functionWhnf lamₙ = lamₙ
functionWhnf (ne x) = ne x

productWhnf : ∀ {p} → Product p → Whnf p
productWhnf prodₙ = prodₙ
productWhnf (ne x) = ne x

⟦_⟧ₙ : (W : BindingType) → ∀ {F G} → Whnf (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ BΠ = Πₙ
⟦_⟧ₙ BΣ = Σₙ


------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Set where
  id    : Wk        -- η : Γ ≤ Γ.
  step  : Wk  → Wk  -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : Wk  → Wk  -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

repeat : {A : Set} → (A → A) → A → Nat → A
repeat f a 0 = a
repeat f a (1+ n) = f (repeat f a n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar ρ x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n        = n
wkVar (step ρ) n        = 1+ (wkVar ρ n)
wkVar (lift ρ) 0    = 0
wkVar (lift ρ) (1+ n) = 1+ (wkVar ρ n)

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : (ρ : Wk) (g : List (GenT Term)) → List (GenT Term)
  wkGen ρ [] = []
  wkGen ρ (⟦ l , t ⟧ ∷ g) = ⟦ l , (wk (repeat lift ρ l) t) ⟧ ∷ wkGen ρ g

  wk : (ρ : Wk) (t : Term) → Term
  wk ρ (var x) = var (wkVar ρ x)
  wk ρ (gen x c) = gen x (wkGen ρ c)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term → Term
wk1 = wk (step id)

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)    = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n) = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ sucₙ    = sucₙ
wkNatural ρ zeroₙ   = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkUnitary : ∀ {t} ρ → Unitary t → Unitary (wk ρ t)
wkUnitary ρ starₙ    = starₙ
wkUnitary ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Πₙ      = Πₙ
wkType ρ Σₙ      = Σₙ
wkType ρ ℕₙ      = ℕₙ
wkType ρ Emptyₙ  = Emptyₙ
wkType ρ Unitₙ = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ {t} ρ → Product t → Product (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Σₙ      = Σₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)

-- Non-dependent version of Π.

_▹▹_ : Term → Term → Term
A ▹▹ B = Π A ▹ wk1 B

-- Non-dependent products.

_××_ : Term → Term → Term
A ×× B = Σ A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Set
Subst = Nat → Term

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst → Term
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst → Subst
tail σ n = σ (1+ n)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst) → Subst
liftSubst σ 0    = var 0
liftSubst σ (1+ x) = wk1Subst σ x

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst : Wk → Subst
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : (σ : Subst) (g : List (GenT Term)) → List (GenT Term)
  substGen σ [] = []
  substGen σ (⟦ l , t ⟧ ∷ g) = ⟦ l , (subst (repeat liftSubst σ l) t) ⟧ ∷ substGen σ g

  subst : (σ : Subst) (t : Term) → Term
  subst σ (var x) = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst → Term → Subst
consSubst σ t 0    = t
consSubst σ t (1+ n) = σ n

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term → Subst
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst → Subst → Subst
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk → Subst → Subst
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst → Wk → Subst
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


-- TODO where should this go? Do i make it a rewrite rule globally?
B-subst : (σ : Subst) (W : BindingType) (F G : Term)
        → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ BΠ F G = PE.refl
B-subst σ BΣ F G = PE.refl
