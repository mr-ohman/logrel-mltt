-- Some proposition constructors.

{-# OPTIONS --without-K --safe #-}

module Tools.Nullary where

open import Tools.Empty

-- Negation.

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

-- Decidable propositions.

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- If A and B are logically equivalent, then so are Dec A and Dec B.

map : ∀ {A B} → (A → B) → (B → A) → Dec A → Dec B
map f g (yes p) = yes (f p)
map f g (no ¬p) = no (λ x → ¬p (g x))
