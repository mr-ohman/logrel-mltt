module Definition.Untyped where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool
open import Data.List


data Term : Set where
  U : Term
  Π_▹_ : Term → Term → Term
  ℕ : Term
  var : Nat → Term
  lam : Term → Term
  _∘_ : Term → Term → Term
  zero : Term
  suc : Term → Term
  natrec : Term → Term → Term → Term

data Neutral : Term → Set where
  var : ∀ n → Neutral (var n)
  _∘_ : ∀ {k u} → Neutral u → Neutral (k ∘ u)
  suc : ∀ {k} → Neutral k → Neutral (suc k)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrec (lam C) c g ∘ k)

_<?_ : Nat → Nat → Bool
zero <? zero = false
zero <? suc n = true
suc m <? zero = false
suc m <? suc n = m <? n

_==_ : (m n : Nat) → Bool
zero == zero = true
zero == suc n = false
suc m == zero = false
suc m == suc n = m == n

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
