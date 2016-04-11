module Definition.Untyped.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Definition.Untyped
open import Relation.Binary.PropositionalEquality hiding ([_])

subst-test : {x : Term} → lam (var zero) [ x ] ≡ lam (var zero)
subst-test = refl
