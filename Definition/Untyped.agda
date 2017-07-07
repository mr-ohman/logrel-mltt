-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K #-}

module Definition.Untyped where

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


infixl 30 _∙_
infix 30 Π_▹_
infixr 22 _▹▹_
infixl 30 _•_ _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (snoc-lists, isomorphic to lists)

data Con (A : Set) : Set where
  ε   : Con A               -- Empty context
  _∙_ : Con A → A → Con A  -- Context extension


-- The Grammar of our language

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

data Term : Set where

  -- Type constructors
  U      : Term                     -- Universe
  Π_▹_   : (A B : Term)     → Term  -- Dependent function type (B is a binder)
  ℕ      : Term                     -- Type of natural numbers

  -- Lambda-calculus
  var    : (x : Nat)        → Term  -- Variable (de Bruijn index)
  lam    : (t : Term)       → Term  -- Function abstraction (binder)
  _∘_    : (t u : Term)     → Term  -- Application

  -- Introduction and elimination of natural numbers
  zero   : Term                     -- Natural number zero
  suc    : (t : Term)       → Term  -- Successor
  natrec : (A t u v : Term) → Term  -- Recursor (A is a binder)


-- Injectivity of term constructors w.r.t. propositional equality

-- If  Π F G = Π H E  then  F = H  and  G = E.

Π-PE-injectivity : ∀ {F G H E} → Term.Π F ▹ G PE.≡ Π H ▹ E → F PE.≡ H × G PE.≡ E
Π-PE-injectivity PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : ∀ {n m} → Term.suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl


-- Neutral terms

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term → Set where
  var    : ∀ n                     → Neutral (var n)
  _∘_    : ∀ {k u}     → Neutral k → Neutral (k ∘ u)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrec C c g k)


-- Weak head normal forms (whnfs)

-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  U    : Whnf U
  Π    : ∀ {A B} → Whnf (Π A ▹ B)
  ℕ    : Whnf ℕ

  -- Introductions are whnfs.
  lam  : ∀ {t} → Whnf (lam t)
  zero : Whnf zero
  suc  : ∀ {t} → Whnf (suc t)

  -- Neutrals are whnfs.
  ne   : ∀ {n} → Neutral n → Whnf n


-- Whnf inequalities

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ℕ : Term.U PE.≢ ℕ
U≢ℕ ()

U≢Π : ∀ {F G} → Term.U PE.≢ Π F ▹ G
U≢Π ()

U≢ne : ∀ {K} → Neutral K → U PE.≢ K
U≢ne () PE.refl

ℕ≢Π : ∀ {F G} → Term.ℕ PE.≢ Π F ▹ G
ℕ≢Π ()

ℕ≢ne : ∀ {K} → Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

Π≢ne : ∀ {F G K} → Neutral K → Π F ▹ G PE.≢ K
Π≢ne () PE.refl

zero≢suc : ∀ {n} → Term.zero PE.≢ suc n
zero≢suc ()

zero≢ne : ∀ {k} → Neutral k → Term.zero PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → Term.suc n PE.≢ k
suc≢ne () PE.refl


-- Several views on whnfs (note: not recursive)

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural : Term → Set where
  zero :                     Natural zero
  suc  : ∀ {t}             → Natural (suc t)
  ne   : ∀ {n} → Neutral n → Natural n

-- A (small) type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Π : ∀ {A B} → Type (Π A ▹ B)
  ℕ : Type ℕ
  ne : ∀{n} → Neutral n → Type n

-- A whnf of type Π A B is either lam t or neutral.

data Function : Term → Set where
  lam : ∀{t} → Function (lam t)
  ne : ∀{n} → Neutral n → Function n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf suc = suc
naturalWhnf zero = zero
naturalWhnf (ne x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Π = Π
typeWhnf ℕ = ℕ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {f} → Function f → Whnf f
functionWhnf lam = lam
functionWhnf (ne x) = ne x

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
  id    : Wk        -- η : Γ ≤ Γ
  step  : Wk  → Wk  -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : Wk  → Wk  -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar ρ x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n       = n
wkVar (step ρ) n       = suc (wkVar ρ n)
wkVar (lift ρ) zero    = zero
wkVar (lift ρ) (suc n) = suc (wkVar ρ n)

-- Weakening of terms.
-- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

wk : (ρ : Wk) (t : Term) → Term
wk ρ U                = U
wk ρ (Π A ▹ B)        = Π wk ρ A ▹ wk (lift ρ) B
wk ρ ℕ                = ℕ
wk ρ (var x)          = var (wkVar ρ x)
wk ρ (lam t)          = lam (wk (lift ρ) t)
wk ρ (t ∘ u)          = wk ρ t ∘ wk ρ u
wk ρ zero             = zero
wk ρ (suc t)          = suc (wk ρ t)
wk ρ (natrec A t u v) = natrec (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term → Term
wk1 = wk (step id)

-- Weakening of a context

wkCon : Wk → Con Term → Con Term
wkCon (step pr) (Γ ∙ x) = wkCon pr Γ ∙ x
wkCon (lift pr) (Γ ∙ x) = wkCon pr Γ ∙ wk pr x
wkCon pr Γ              = Γ

-- Weakening of a neutral term

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (_∘_ n)    = _∘_ (wkNeutral ρ n)
wkNeutral ρ (natrec n) = natrec (wkNeutral ρ n)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ suc    = suc
wkNatural ρ zero   = zero
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Π      = Π
wkType ρ ℕ      = ℕ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lam    = lam
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ U      = U
wkWhnf ρ Π      = Π
wkWhnf ρ ℕ      = ℕ
wkWhnf ρ lam    = lam
wkWhnf ρ zero   = zero
wkWhnf ρ suc    = suc
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

-- Non-dependent version of Π

_▹▹_ : Term → Term → Term
A ▹▹ B = Π A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Set
Subst = Nat → Term

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.

head : Subst → Term
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.

tail : Subst → Subst
tail σ n = σ (suc n)

-- Substitution of a variable.

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.

idSubst : Subst
idSubst = var

-- Weaken a substitution by one.

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.

liftSubst : (σ : Subst) → Subst
liftSubst σ zero    = var zero
liftSubst σ (suc x) = wk1Subst σ x

-- Transform a weakening into a substitution.

toSubst : Wk → Subst
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.

subst : (σ : Subst) (t : Term) → Term
subst σ U          = U
subst σ (Π A ▹ B) = Π subst σ A ▹ subst (liftSubst σ) B
subst σ ℕ          = ℕ
subst σ (var x)    = substVar σ x
subst σ (lam t)    = lam (subst (liftSubst σ) t)
subst σ (t ∘ u)    = (subst σ t) ∘ (subst σ u)
subst σ zero       = zero
subst σ (suc t)    = suc (subst σ t)
subst σ (natrec A t u v) =
  natrec (subst (liftSubst σ) A) (subst σ t) (subst σ u) (subst σ v)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.

consSubst : Subst → Term → Subst
consSubst σ t zero    = t
consSubst σ t (suc n) = σ n

-- Compose two substitutions.

_ₛ•ₛ_ : Subst → Subst → Subst
_ₛ•ₛ_ σ σ' x = subst σ (σ' x)

-- Composition of weakening and substitution.

_•ₛ_ : Wk → Subst → Subst
_•ₛ_ ρ σ x = wk ρ (σ x)

_ₛ•_ : Subst → Wk → Subst
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (consSubst idSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t
