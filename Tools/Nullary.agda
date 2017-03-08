{-# OPTIONS --without-K #-}

module Tools.Nullary where

open import Tools.Empty

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

map : ∀ {A B} → (A → B) → (B → A) → Dec A → Dec B
map f g (yes p) = yes (f p)
map f g (no ¬p) = no (λ x → ¬p (g x))
