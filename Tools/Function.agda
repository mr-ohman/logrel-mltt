{-# OPTIONS --without-K --safe #-}

module Tools.Function where

-- Identity function
idᶠ : {A : Set} → A → A
idᶠ x = x

-- Function composition (simply typed variant)
_∘ᶠ_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘ᶠ_ f g a = f (g a)
