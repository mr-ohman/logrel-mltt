module Definition.LogicalRelation.Consequences.InverseUniv where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation.Consequences.Syntactic

import Tools.Sum as Sum
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary

data UFull : Term → Set where
  U  : UFull U
  Π₁ : ∀ {F G} → UFull F → UFull (Π F ▹ G)
  Π₂ : ∀ {F G} → UFull G → UFull (Π F ▹ G)

noU : ∀ {t A Γ} → Γ ⊢ t ∷ A → ¬ (UFull t)
noU (ℕ x) ()
noU (Π t ▹ t₁) (Π₁ ufull) = noU t ufull
noU (Π t ▹ t₁) (Π₂ ufull) = noU t₁ ufull
noU (var x₁ x₂) ()
noU (lam x t₁) ()
noU (t ∘ t₁) ()
noU (zero x) ()
noU (suc t) ()
noU (natrec x t t₁ t₂) ()
noU (conv t₁ x) ufull = noU t₁ ufull

pilem : ∀ {F G H E}
      → (¬ UFull (Π F ▹ G)) ⊎ (¬ UFull (Π H ▹ E))
      → (¬ UFull F) ⊎ (¬ UFull H) × (¬ UFull G) ⊎ (¬ UFull E)
pilem (inj₁ x) = inj₁ (λ x₁ → x (Π₁ x₁)) , inj₁ (λ x₁ → x (Π₂ x₁))
pilem (inj₂ x) = inj₂ (λ x₁ → x (Π₁ x₁)) , inj₂ (λ x₁ → x (Π₂ x₁))

inverseUniv : ∀ {A Γ} → ¬ (UFull A) → Γ ⊢ A → Γ ⊢ A ∷ U
inverseUniv q (ℕ x) = ℕ x
inverseUniv q (U x) = ⊥-elim (q U)
inverseUniv q (Π A ▹ A₁) = Π inverseUniv (λ x → q (Π₁ x)) A ▹ inverseUniv (λ x → q (Π₂ x)) A₁
inverseUniv q (univ x) = x

inverseUnivEq' : ∀ {A B Γ} → (¬ (UFull A)) ⊎ (¬ (UFull B)) → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq' q (univ x) = x
inverseUnivEq' q (refl x) = refl (inverseUniv (Sum.id q) x)
inverseUnivEq' q (sym A≡B) = sym (inverseUnivEq' (Sum.sym q) A≡B)
inverseUnivEq' (inj₁ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq' (inj₁ x) A≡B
      _ , _ , t = syntacticEqTerm w
      y = noU t
  in  trans w (inverseUnivEq' (inj₁ y) A≡B₁)
inverseUnivEq' (inj₂ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq' (inj₂ x) A≡B₁
      _ , t , _ = syntacticEqTerm w
      y = noU t
  in  trans (inverseUnivEq' (inj₂ y) A≡B) w
inverseUnivEq' q (Π-cong x A≡B A≡B₁) =
  let w , e = pilem q
  in  Π-cong x (inverseUnivEq' w A≡B) (inverseUnivEq' e A≡B₁)

inverseUnivEq : ∀ {A B Γ} → Γ ⊢ A ∷ U → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq A A≡B = inverseUnivEq' (inj₁ (noU A)) A≡B
