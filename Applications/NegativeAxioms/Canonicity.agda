-- Prove that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

module Applications.NegativeAxioms.Canonicity where

open import Definition.Typed
open import Definition.Untyped as U
open import Definition.Conversion.FullReduction

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Unit

-- Contexts of only negative hypotheses

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m : Nat
    x : Fin m
    Γ : Con Term m
    A B C : Term m
    t u : Term m

-- A context is inconsistent if it allows us to derive absurdity.

Inconsistent : Cxt m → Set
Inconsistent Γ = ∃ λ t → Γ ⊢ t ∷ Empty

-- A choiceful type can only be eliminated through branching
-- (via a recursor).

data Choiceful : Ty m → Set where
  empty : Choiceful {m = m} Empty
  nat   : Choiceful {m = m} ℕ

-- A type is negative if it is normal enough to see that its ending in ⊥,
-- and it is actually ending in ⊥.
-- Think: ¬A.

data NegativeType : Ty m → Set where
  empty : NegativeType {m = m} Empty
  pi    : NegativeType B → NegativeType (Π A ▹ B)
  sigma : NegativeType A → NegativeType B → NegativeType (Σ A ▹ B)

-- A context is negative if all of its type entries are negative.

data NegativeContext : Con Ty m → Set where
  ε   : NegativeContext ε
  _∙_ : NegativeContext Γ → NegativeType A → NegativeContext (Γ ∙ A)

lookupNegative : NegativeContext Γ → (x ∷ A ∈ Γ) → NegativeType A
lookupNegative (nΓ ∙ nA) here      = {! nA !}  -- need to weaken predicate
lookupNegative (nΓ ∙ nA) (there h) = {!lookupNegative nΓ h!}

-- If we can prove something in a negative context,
-- we can also prove absurdity.

-- We show this for normal proofs.

module NegativeNeProvesFalse (nΓ : NegativeContext Γ) where

  hyp : ⊢ Γ → x ∷ A ∈ Γ → Choiceful A → Inconsistent Γ
  hyp ⊢Γ h cA with lookupNegative nΓ h
  hyp ⊢Γ h empty | empty = var _ , var ⊢Γ h

  lem : Choiceful A
      → (d : Γ ⊢ u ∷ A)
      → (n : NfNeutral u)
      → Inconsistent Γ
  lem cA (var ⊢Γ h       ) (var _           ) = hyp ⊢Γ h cA
  lem cA (d ∘ⱼ _         ) (∘ₙ n _          ) = lem {!!} d n
  lem cA (fstⱼ _ _ d     ) (fstₙ n          ) = lem {!!} d n
  lem cA (sndⱼ _ _ d     ) (sndₙ n          ) = lem {!!} d n
  lem cA (natrecⱼ _ _ _ d) (natrecₙ _ _ _ n ) = lem {!!} d n
  lem cA (Emptyrecⱼ _ d  ) (Emptyrecₙ _ _   ) = _ , d
  lem cA (conv d _       ) n                  = lem {!!} d n  -- impossible

-- -}
-- -}
-- -}
-- -}
