{-# OPTIONS --without-K #-}

module Definition.Untyped.AltSubst where

-- Alternative substitution, based on implementation from
-- Benjamin C. Pierce's Types and Programming Languages.

open import Definition.Untyped

open import Tools.Nat
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Relation.Nullary.Decidable using (⌊_⌋)


_<?_ : Nat → Nat → Bool
m <? n = ⌊ suc m ≤? n ⌋

_==_ : (m n : Nat) → Bool
m == n =  ⌊ m ≟ n ⌋

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
