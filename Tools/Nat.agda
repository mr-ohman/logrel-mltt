-- The natural numbers.

{-# OPTIONS --without-K #-}

module Tools.Nat where

open import Tools.PropositionalEquality
open import Tools.Nullary

-- We reexport Agda′s built-in type of natural numbers.

open import Agda.Builtin.Nat using (Nat; zero; suc) public

infix 4 _≟_

-- Predecessor, cutting off at 0.

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- Decision of number equality.

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (subst (λ y → m ≡ pred y) x refl))
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()
