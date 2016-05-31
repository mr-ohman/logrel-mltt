module Definition.Untyped where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Tools.Context

infix 30 Π_▹_
data Term : Set where
  U : Term
  Π_▹_ : Term → Term → Term  -- second argument is a binder
  ℕ : Term
  var : Nat → Term
  lam : Term → Term  -- binder
  _∘_ : Term → Term → Term
  zero : Term
  suc : Term → Term
  natrec : Term → Term → Term → Term → Term -- first argument is a binder

data Neutral : Term → Set where
  var : ∀ n → Neutral (var n)
  _∘_ : ∀ {k u} → Neutral k → Neutral (k ∘ u)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrec C c g k)

data Natural : Term → Set where
  suc : ∀ {n} → Natural n → Natural (suc n)
  zero : Natural zero
  ne : ∀ {n} → Neutral n → Natural n

data [Natural] (R : Term → Term → Set) : Term → Term → Set where
  suc : ∀ {n n'} → [Natural] R n n' → [Natural] R (suc n) (suc n')
  zero : [Natural] R zero zero
  ne : ∀ {n n'} → Neutral n → Neutral n' → R n n' → [Natural] R n n'

-- Weak head normal forms

data Whnf : Term → Set where
  U : Whnf U
  Π : ∀ {A B} → Whnf (Π A ▹ B)
  ℕ : Whnf ℕ
  lam : ∀{t} → Whnf (lam t)
  zero : Whnf zero
  suc  : ∀{t} → Whnf (suc t)
  ne : ∀{n} → Neutral n → Whnf n


data Wk : Set where
  id    : Wk
  step  : Wk  → Wk
  lift  : Wk  → Wk

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

wkNat : (ρ : Wk) (n : Nat) → Nat
wkNat id n = n
wkNat (step ρ) n = suc (wkNat ρ n)
wkNat (lift ρ) zero = zero
wkNat (lift ρ) (suc n) = suc (wkNat ρ n)

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


-- module WellScoped where
--   wkNat : {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) (n : Nat) → Nat
--   wkNat base n = n
--   wkNat (step ρ) n = suc (wkNat ρ n)
--   wkNat (lift ρ) zero = zero
--   wkNat (lift ρ) (suc n) = suc (wkNat ρ n)

--   wk : {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) (t : Term) → Term
--   wk ρ U = U
--   wk ρ (Π t ▹ t₁) = Π wk ρ t ▹ wk (lift ρ) t₁
--   wk ρ ℕ = ℕ
--   wk ρ (var x) = var (wkNat ρ x)
--   wk ρ (lam t) = lam (wk (lift ρ) t)
--   wk ρ (t ∘ t₁) = (wk ρ t) ∘ (wk ρ t₁)
--   wk ρ zero = zero
--   wk ρ (suc t) = suc (wk ρ t)
--   wk ρ (natrec t t₁ t₂) = natrec (wk (lift ρ) t) (wk ρ t₁) (wk ρ t₂)


-- TODO prove ∀ {Γ Δ} (ρ : Γ ⊆ Δ) t → WellScoped.wk ρ t ≡ wk (toWk ρ) t

wk1 : Term → Term
wk1 = wk (step id)

Subst = Nat → Term

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

wkSubst : Wk → Subst → Subst
wkSubst pr σ x = wk pr (σ x)

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

idSubst : Subst
idSubst = var

liftSubst : (σ : Subst) → Subst
liftSubst σ zero = var zero
liftSubst σ (suc x) = wk1Subst σ x

toSubst : Wk → Subst
toSubst pr x = var (wkNat pr x)

purge : Wk → Subst → Subst
purge pr σ x = σ (wkNat pr x)

subst : (σ : Subst) (t : Term) → Term
subst σ U = U
subst σ (Π t ▹ t₁) = Π subst σ t ▹ subst (liftSubst σ) t₁
subst σ ℕ = ℕ
subst σ (var x) = substVar σ x
subst σ (lam t) = lam (subst (liftSubst σ) t)
subst σ (t ∘ t₁) = (subst σ t) ∘ (subst σ t₁)
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (natrec t t₁ t₂ t₃) = natrec (subst (liftSubst σ) t) (subst σ t₁) (subst σ t₂) (subst σ t₃)

consSubst : Subst → Term → Subst
consSubst s t zero = t
consSubst s t (suc n) = s n

infix 25 _[_]
_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (consSubst idSubst s) t

infix 25 _[_]↑
_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t

infixr 22 _▹▹_
_▹▹_ : Term → Term → Term
A ▹▹ B = Π A ▹ wk1 B

wkCon : Wk → Con Term → Con Term
wkCon (step pr) (Γ ∙ x) = wkCon pr Γ ∙ x
wkCon (lift pr) (Γ ∙ x) = wkCon pr Γ ∙ wk pr x
wkCon pr Γ = Γ

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n) = var (wkNat ρ n)
wkNeutral ρ (_∘_ n) = _∘_ (wkNeutral ρ n)
wkNeutral ρ (natrec n) = natrec (wkNeutral ρ n)

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ (suc n₁) = suc (wkNatural ρ n₁)
wkNatural ρ zero = zero
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wk[Natural] : ∀ {t u R R'} ρ
            → (∀ {t' u'} → R t' u' → R' (wk ρ t') (wk ρ u'))
            → [Natural] R t u
            → [Natural] R' (wk ρ t) (wk ρ u)
wk[Natural] ρ wkR (suc [n]) = suc (wk[Natural] ρ wkR [n])
wk[Natural] ρ wkR zero = zero
wk[Natural] ρ wkR (ne x x₁ x₂) = ne (wkNeutral ρ x) (wkNeutral ρ x₁) (wkR x₂)

-- Alternative substitution, based on implementation from
-- Benjamin C. Pierce's Types and Programming Languages.

_<?_ : Nat → Nat → Bool
m <? n = ⌊ suc m ≤? n ⌋
-- zero <? zero = false
-- zero <? suc n = true
-- suc m <? zero = false
-- suc m <? suc n = m <? n

_==_ : (m n : Nat) → Bool
m == n =  ⌊ m ≟ n ⌋
-- zero == zero = true
-- zero == suc n = false
-- suc m == zero = false
-- suc m == suc n = m == n

↑ : (Nat → Nat) → Nat → Term → Term
↑ d c U = U
↑ d c (Π t ▹ t₁) = Π ↑ d c t ▹ ↑ d (suc c) t₁
↑ d c ℕ = ℕ
↑ d c (var x) = if x <? c then var x else var (d x)
↑ d c (lam t) = lam (↑ d (suc c) t)
↑ d c (t ∘ t₁) = ↑ d c t ∘ ↑ d c t₁
↑ d c zero = zero
↑ d c (suc t) = suc (↑ d c t)
↑ d c (natrec t t₁ t₂ t₃) = natrec (↑ d c t) (↑ d c t₁) (↑ d c t₂) (↑ d c t₃)

_↦_ : Nat → Term → Term → Term
_↦_ j s U = U
_↦_ j s (Π t ▹ t₁) = Π (j ↦ s) t ▹ (suc j ↦ ↑ suc 0 s) t₁
_↦_ j s ℕ = ℕ
_↦_ j s (var x) = if x == j then s else var x
_↦_ j s (lam t) = lam ((suc j ↦ ↑ suc 0 s) t)
_↦_ j s (t ∘ t₁) = ((j ↦ s) t) ∘ ((j ↦ s) t₁)
_↦_ j s zero = zero
_↦_ j s (suc t) = suc ((j ↦ s) t)
_↦_ j s (natrec t t₁ t₂ t₃) = natrec ((j ↦ s) t) ((j ↦ s) t₁) ((j ↦ s) t₂) ((j ↦ s) t₃)
