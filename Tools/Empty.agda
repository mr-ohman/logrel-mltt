module Tools.Empty where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
