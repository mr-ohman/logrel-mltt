module Definition.Untyped where

postulate TODO : ∀{a}{A : Set a} → A

open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List
open import Data.Unit using (⊤)

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

wkNat : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (n : Nat) → Nat
wkNat base n = n
wkNat (step ρ) n = suc (wkNat ρ n)
wkNat (pop! ρ) zero = zero
wkNat (pop! ρ) (suc n) = suc (wkNat ρ n)

wk : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (t : Term) → Term
wk ρ U = U
wk ρ (Π t ▹ t₁) = Π wk ρ t ▹ wk (pop! ρ) t₁
wk ρ ℕ = TODO
wk ρ (var x) = var (wkNat ρ x)
wk ρ (lam t) = TODO
wk ρ (t ∘ t₁) = TODO
wk ρ zero = TODO
wk ρ (suc t) = TODO
wk ρ (natrec t t₁ t₂) = TODO

wk1 : Term → Term
wk1 = TODO

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

substVar : (σ : Subst) (x : Nat) → Term
substVar [] x = var x  -- garbage case, should not happen
substVar (t ∷ σ) zero = t
substVar (t ∷ σ) (suc x) = substVar σ x

wk1Subst : Nat → Subst → Subst
wk1Subst n = List.map TODO -- (wk (step (⊆-refl {! n !})))

liftSubst : (σ : Subst) → Subst
liftSubst σ = var 0 ∷ wk1Subst TODO σ

subst : (σ : Subst) (t : Term) → Term
subst σ U = TODO
subst σ (Π t ▹ t₁) = TODO
subst σ ℕ = TODO
subst σ (var x) = TODO
subst σ (lam t) = lam (subst (liftSubst σ) t)
subst σ (t ∘ t₁) = TODO
subst σ zero = TODO
subst σ (suc t) = TODO
subst σ (natrec t t₁ t₂) = TODO

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
t [ s ] = ↑ pred 0 ((0 ↦ s) t)
