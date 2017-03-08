{-# OPTIONS --without-K #-}

module Tools.Empty where

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
