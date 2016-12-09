module Definition.Untyped where

open import Tools.Nat
open import Tools.Product


infixl 30 _∙_
infix 30 Π_▹_
infixr 22 _▹▹_
infix 25 _[_]
infix 25 _[_]↑


-- Context for the language (effectively the same as a list).

data Con (A : Set) : Set where
  ε   : Con A
  _∙_ : Con A → A → Con A


-- Grammar of language.

data Term : Set where
  U      : Term
  Π_▹_   : Term → Term → Term                 -- second argument is a binder
  ℕ      : Term
  var    : Nat  → Term
  lam    : Term → Term                        -- binder
  _∘_    : Term → Term → Term
  zero   : Term
  suc    : Term → Term
  natrec : Term → Term → Term → Term → Term   -- first argument is a binder


-- A view of terms which cannot reduce due to free variable.

data Neutral : Term → Set where
  var    : ∀ n                     → Neutral (var n)
  _∘_    : ∀ {k u}     → Neutral k → Neutral (k ∘ u)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrec C c g k)


-- Weak head normal forms

data Whnf : Term → Set where
  U : Whnf U
  Π : ∀ {A B} → Whnf (Π A ▹ B)
  ℕ : Whnf ℕ
  lam : ∀{t} → Whnf (lam t)
  zero : Whnf zero
  suc  : ∀{t} → Whnf (suc t)
  ne : ∀{n} → Neutral n → Whnf n


-- A partial view on whnfs of natural number terms.
-- Note: not inductive.

data Natural : Term → Set where
  suc  : ∀ {n}             → Natural (suc n)
  zero :                     Natural zero
  ne   : ∀ {n} → Neutral n → Natural n

-- Natural is a subset of Whnf

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf suc = suc
naturalWhnf zero = zero
naturalWhnf (ne x) = ne x


-- A partial view on two whnfs of natural number terms.
-- Note: not inductive.

-- data [Natural] : Term → Term → Set where
--   suc  : ∀ {n n'}                          → [Natural] (suc n) (suc n')
--   zero :                                     [Natural] zero zero
--   ne   : ∀ {n n'} → Neutral n → Neutral n' → [Natural] n n'

-- -- Properties of [Natural]

-- reflNatural : ∀ {n} → Natural n → [Natural] n n
-- reflNatural suc = suc
-- reflNatural zero = zero
-- reflNatural (ne x) = ne x x

-- symNatural : ∀ {m n} → [Natural] m n → [Natural] n m
-- symNatural suc = suc
-- symNatural zero = zero
-- symNatural (ne x x₁) = ne x₁ x

-- transNatural : ∀ {n n' n''}
--              → [Natural] n  n'
--              → [Natural] n' n''
--              → [Natural] n  n''
-- transNatural suc suc = suc
-- transNatural suc (ne () n')
-- transNatural zero n' = n'
-- transNatural (ne neN ()) suc
-- transNatural (ne neN neN') zero = ne neN neN'
-- transNatural (ne neN neN') (ne neN'₁ neN'') = ne neN neN''

-- split : ∀ {t u} → [Natural] t u → Natural t × Natural u
-- split suc = suc , suc
-- split zero = zero , zero
-- split (ne x x₁) = ne x , ne x₁

------------------------------------------------------------------------
-- Weakening

data Wk : Set where
  id    : Wk
  step  : Wk  → Wk
  lift  : Wk  → Wk

-- Composition of weakening.

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

-- Weakening of variables.

wkNat : (ρ : Wk) (n : Nat) → Nat
wkNat id n = n
wkNat (step ρ) n = suc (wkNat ρ n)
wkNat (lift ρ) zero = zero
wkNat (lift ρ) (suc n) = suc (wkNat ρ n)

-- Weakening of terms.

wk : (ρ : Wk) (t : Term) → Term
wk ρ U = U
wk ρ (Π t ▹ t₁) = Π wk ρ t ▹ wk (lift ρ) t₁
wk ρ ℕ = ℕ
wk ρ (var x) = var (wkNat ρ x)
wk ρ (lam t) = lam (wk (lift ρ) t)
wk ρ (t ∘ t₁) = (wk ρ t) ∘ (wk ρ t₁)
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec t t₁ t₂ t₃) = natrec (wk (lift ρ) t) (wk ρ t₁) (wk ρ t₂) (wk ρ t₃)

wk1 : Term → Term
wk1 = wk (step id)

-- Weakening of a context.

wkCon : Wk → Con Term → Con Term
wkCon (step pr) (Γ ∙ x) = wkCon pr Γ ∙ x
wkCon (lift pr) (Γ ∙ x) = wkCon pr Γ ∙ wk pr x
wkCon pr Γ = Γ

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n) = var (wkNat ρ n)
wkNeutral ρ (_∘_ n) = _∘_ (wkNeutral ρ n)
wkNeutral ρ (natrec n) = natrec (wkNeutral ρ n)

-- Weakening of an instance of the Natural view.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ suc = suc
wkNatural ρ zero = zero
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ U = U
wkWhnf ρ Π = Π
wkWhnf ρ ℕ = ℕ
wkWhnf ρ lam = lam
wkWhnf ρ zero = zero
wkWhnf ρ suc = suc
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

-- Weakening of an instance of the [Natural] view.

-- wk[Natural] : ∀ {t u} ρ
--             → [Natural] t u
--             → [Natural] (wk ρ t) (wk ρ u)
-- wk[Natural] ρ (suc {t} {u}) = suc {wk ρ t} {wk ρ u}
-- wk[Natural] ρ zero = zero
-- wk[Natural] ρ (ne x x₁) = ne (wkNeutral ρ x) (wkNeutral ρ x₁)

-- Non-dependent version of Π.
_▹▹_ : Term → Term → Term
A ▹▹ B = Π A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

Subst : Set
Subst = Nat → Term

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

-- Apply a weakening to a substitution such that
-- the substitution is applied first when applying to a term.

wkSubst : Wk → Subst → Subst
wkSubst pr σ x = wk pr (σ x)

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Identity substitution.

idSubst : Subst
idSubst = var

-- Lift a substitution.

liftSubst : (σ : Subst) → Subst
liftSubst σ zero = var zero
liftSubst σ (suc x) = wk1Subst σ x

-- Transform a weakening into a substitution.

toSubst : Wk → Subst
toSubst pr x = var (wkNat pr x)

-- Apply a weakening to a substitution such that
-- the weakening is applied first when applying to a term.

purge : Wk → Subst → Subst
purge pr σ x = σ (wkNat pr x)

-- Apply a substitution to a term.

subst : (σ : Subst) (t : Term) → Term
subst σ U = U
subst σ (Π t ▹ t₁) = Π subst σ t ▹ subst (liftSubst σ) t₁
subst σ ℕ = ℕ
subst σ (var x) = substVar σ x
subst σ (lam t) = lam (subst (liftSubst σ) t)
subst σ (t ∘ t₁) = (subst σ t) ∘ (subst σ t₁)
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (natrec t t₁ t₂ t₃) =
  natrec (subst (liftSubst σ) t) (subst σ t₁) (subst σ t₂) (subst σ t₃)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.

consSubst : Subst → Term → Subst
consSubst σ t zero = t
consSubst σ t (suc n) = σ n

-- Compose two substitutions.

substComp : Subst → Subst → Subst
substComp σ σ' n = subst σ' (σ n)

-- Substitute the first variable of a term with an other term.

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (consSubst idSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t
