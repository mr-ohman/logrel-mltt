module Definition.Untyped where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Tools.Context

data Term : Set where
  U : Term
  Π_▹_ : Term → Term → Term  -- second argument is a binder
  ℕ : Term
  var : Nat → Term
  lam : Term → Term  -- binder
  _∘_ : Term → Term → Term
  zero : Term
  suc : Term → Term
  natrec : Term → Term → Term → Term -- first argument is a binder

data Neutral : Term → Set where
  var : ∀ n → Neutral (var n)
  _∘_ : ∀ {k u} → Neutral u → Neutral (k ∘ u)
  suc : ∀ {k} → Neutral k → Neutral (suc k)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrec C c g ∘ k)

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

-- Possibly a bit too generous, but it should not cause any harm
size : Term → Nat
size U = zero
size (Π t ▹ t₁) = suc (size t) ⊔ size t₁
size ℕ = zero
size (var x) = suc x
size (lam t) = suc (size t)
size (t ∘ t₁) = size t ⊔ size t₁
size zero = zero
size (suc t) = size t
size (natrec t t₁ t₂) = suc (size t) ⊔ size t₁ ⊔ size t₂

wkNat : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (n : Nat) → Nat
wkNat base n = n
wkNat (step ρ) n = suc (wkNat ρ n)
wkNat (lift ρ) zero = zero
wkNat (lift ρ) (suc n) = suc (wkNat ρ n)

wk : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (t : Term) → Term
wk ρ U = U
wk ρ (Π t ▹ t₁) = Π wk ρ t ▹ wk (lift ρ) t₁
wk ρ ℕ = ℕ
wk ρ (var x) = var (wkNat ρ x)
wk ρ (lam t) = lam (wk (lift ρ) t)
wk ρ (t ∘ t₁) = (wk ρ t) ∘ (wk ρ t₁)
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec t t₁ t₂) = natrec (wk (lift ρ) t) (wk ρ t₁) (wk ρ t₂)

wk1 : (Γ : Con ⊤) → Term → Term
wk1 Γ = wk (step (⊆-refl Γ))

↑ : (Nat → Nat) → Nat → Term → Term
↑ d c U = U
↑ d c (Π t ▹ t₁) = Π ↑ d c t ▹ ↑ d (suc c) t₁
↑ d c ℕ = ℕ
↑ d c (var x) = if x <? c then var x else var (d x)
↑ d c (lam t) = lam (↑ d (suc c) t)
↑ d c (t ∘ t₁) = ↑ d c t ∘ ↑ d c t₁
↑ d c zero = zero
↑ d c (suc t) = suc (↑ d c t)
↑ d c (natrec t t₁ t₂) = natrec (↑ d c t) (↑ d c t₁) (↑ d c t₂)

Subst = List Term

fromCon : ∀ {A} → Con A → Nat
fromCon ε = zero
fromCon (Γ ∙ x) = suc (fromCon Γ)

toCon : Nat → Con ⊤
toCon zero = ε
toCon (suc n) = toCon n ∙ tt

substVar : (σ : Subst) (x : Nat) → Term
substVar [] x = var x  -- garbage case, should not happen
substVar (t ∷ σ) zero = t
substVar (t ∷ σ) (suc x) = substVar σ x

wk1Subst : Nat → Subst → Subst
wk1Subst n = List.map (wk1 (toCon n))

idSubst : (n : Nat) → Subst
idSubst zero = []
idSubst (suc n) = var zero ∷ wk1Subst n (idSubst n)

liftSubst : Nat → (σ : Subst) → Subst
liftSubst n σ = var 0 ∷ wk1Subst n σ

subst : (σ : Subst) (t : Term) → Term
subst σ U = U
subst σ (Π t ▹ t₁) = Π subst σ t ▹ subst (liftSubst (size t) σ) t₁
subst σ ℕ = ℕ
subst σ (var x) = substVar σ x
subst σ (lam t) = lam (subst (liftSubst (size t) σ) t)
subst σ (t ∘ t₁) = (subst σ t) ∘ (subst σ t₁)
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (natrec t t₁ t₂) = natrec (subst (liftSubst (size t) σ) t) (subst σ t₁) (subst σ t₂)

_↦_ : Nat → Term → Term → Term
_↦_ j s U = U
_↦_ j s (Π t ▹ t₁) = Π (j ↦ s) t ▹ (suc j ↦ ↑ suc 0 s) t₁
_↦_ j s ℕ = ℕ
_↦_ j s (var x) = if x == j then s else var x
_↦_ j s (lam t) = lam ((suc j ↦ ↑ suc 0 s) t)
_↦_ j s (t ∘ t₁) = ((j ↦ s) t) ∘ ((j ↦ s) t₁)
_↦_ j s zero = zero
_↦_ j s (suc t) = suc ((j ↦ s) t)
_↦_ j s (natrec t t₁ t₂) = natrec ((j ↦ s) t) ((j ↦ s) t₁) ((j ↦ s) t₂)

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (s ∷ idSubst (size t)) t
