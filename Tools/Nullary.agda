{-# OPTIONS --without-K #-}

module Tools.Nullary where

open import Tools.Empty

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
