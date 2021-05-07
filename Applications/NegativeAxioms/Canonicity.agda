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

Choiceful : Ty m → Set
-- Types: yes
Choiceful (gen Emptykind _)               = ⊤
Choiceful (gen Natkind _)                 = ⊤
-- Types: no
Choiceful (gen Pikind _)                  = ⊥
Choiceful (gen Sigmakind _)               = ⊥
Choiceful (gen Unitkind _)                = ⊥
Choiceful (gen Ukind _)                   = ⊥
-- Terms: no
Choiceful (var _)                         = ⊥
Choiceful (gen Lamkind _)                 = ⊥
Choiceful (gen Appkind _)                 = ⊥
Choiceful (gen Prodkind _)                = ⊥
Choiceful (gen Fstkind _)                 = ⊥
Choiceful (gen Sndkind _)                 = ⊥
Choiceful (gen Zerokind _)                = ⊥
Choiceful (gen Suckind _)                 = ⊥
Choiceful (gen Natreckind _)              = ⊥
Choiceful (gen Starkind _)                = ⊥
Choiceful (gen Emptyreckind _)            = ⊥

-- A type is negative if it is normal enough to see that its ending in ⊥,
-- and it is actually ending in ⊥.
-- Think: ¬A.

NegativeType : Ty m → Set
-- Types: yes
NegativeType (gen Emptykind _)               = ⊤
NegativeType (gen Pikind (A ∷ (B ∷ [])))     = NegativeType B
NegativeType (gen Sigmakind (A ∷ (B ∷ [])))  = NegativeType A × NegativeType B
-- Types: no
NegativeType (gen Natkind _)                 = ⊥
NegativeType (gen Unitkind _)                = ⊥
NegativeType (gen Ukind _)                   = ⊥
-- Terms: no
NegativeType (var _)                         = ⊥
NegativeType (gen Lamkind _)                 = ⊥
NegativeType (gen Appkind _)                 = ⊥
NegativeType (gen Prodkind _)                = ⊥
NegativeType (gen Fstkind _)                 = ⊥
NegativeType (gen Sndkind _)                 = ⊥
NegativeType (gen Zerokind _)                = ⊥
NegativeType (gen Suckind _)                 = ⊥
NegativeType (gen Natreckind _)              = ⊥
NegativeType (gen Starkind _)                = ⊥
NegativeType (gen Emptyreckind _)            = ⊥

-- A context is negative if all of its type entries are negative.

NegativeContext : Con Ty m → Set
NegativeContext ε       = ⊤
NegativeContext (Γ ∙ A) = NegativeContext Γ × NegativeType A

lookupNegative : NegativeContext Γ → (x ∷ A ∈ Γ) → NegativeType A
lookupNegative (nΓ , nA) here      = {! nA !}  -- need to weaken predicate
lookupNegative (nΓ , nA) (there h) = {!lookupNegative nΓ h!}

-- If we can prove something in a negative context,
-- we can also prove absurdity.

-- We show this for normal proofs.

module NegativeNeProvesFalse (nΓ : NegativeContext Γ) where

  hyp : (x ∷ A ∈ Γ) → Choiceful A → Inconsistent Γ
  hyp {A = A} h cA with lookupNegative nΓ h
  ... | z = {!!}

{-
  lem : (d : Γ ⊢ u ∷ A)
      → (n : NfNeutral u)
      → ∃ λ t → Γ ⊢ t ∷ Empty
  lem (var x x₁       ) (var _             ) = {!!}
  lem (d ∘ⱼ _         ) (∘ₙ n _            ) = lem d n
  lem (fstⱼ _ _ d     ) (fstₙ n            ) = lem d n
  lem (sndⱼ _ _ d     ) (sndₙ n            ) = lem d n
  lem (natrecⱼ _ _ _ d) (natrecₙ _ _ _ n) = lem d n
  lem (Emptyrecⱼ _ d  ) (Emptyrecₙ _ _    ) = _ , d
  lem (conv d _       ) n                    = lem d n

-- -}
-- -}
-- -}
-- -}
