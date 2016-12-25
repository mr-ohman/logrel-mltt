{-# OPTIONS --without-K #-}

module Tools.Nat where

open import Tools.PropositionalEquality
open import Tools.Nullary

open import Agda.Builtin.Nat using (Nat; zero; suc) public

infix 4 _≟_

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (subst (λ y → m ≡ pred y) x refl))
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()
