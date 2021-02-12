{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.InverseUniv where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Consequences.Syntactic

open import Tools.Nat
import Tools.Sum as Sum
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary

private
  variable
    n : Nat
    Γ : Con Term n
    A F H : Term n
    G E : Term (1+ n)

-- Proposition for terms if they contain a U.
data UFull : Term n → Set where
  ∃U  : UFull {n} U
  ∃Π₁ : UFull F → UFull (Π F ▹ G)
  ∃Π₂ : UFull G → UFull (Π F ▹ G)
  ∃Σ₁ : UFull F → UFull (Σ F ▹ G)
  ∃Σ₂ : UFull G → UFull (Σ F ▹ G)

-- Terms cannot contain U.
noU : ∀ {t A} → Γ ⊢ t ∷ A → ¬ (UFull t)
noU (ℕⱼ x) ()
noU (Emptyⱼ x) ()
noU (Πⱼ t ▹ t₁) (∃Π₁ ufull) = noU t ufull
noU (Πⱼ t ▹ t₁) (∃Π₂ ufull) = noU t₁ ufull
noU (Σⱼ t ▹ t₁) (∃Σ₁ ufull) = noU t ufull
noU (Σⱼ t ▹ t₁) (∃Σ₂ ufull) = noU t₁ ufull
noU (var x₁ x₂) ()
noU (lamⱼ x t₁) ()
noU (t ∘ⱼ t₁) ()
noU (zeroⱼ x) ()
noU (sucⱼ t) ()
noU (natrecⱼ x t t₁ t₂) ()
noU (Emptyrecⱼ x t) ()
noU (conv t₁ x) ufull = noU t₁ ufull

-- Neutrals cannot contain U.
noUNe : Neutral A → ¬ (UFull A)
noUNe (var n) ()
noUNe (∘ₙ neA) ()
noUNe (natrecₙ neA) ()
noUNe (Emptyrecₙ neA) ()

-- Helper function where if at least one Π-type does not contain U,
-- one of F and H will not contain U and one of G and E will not contain U.
pilem : (¬ UFull (Π F ▹ G)) ⊎ (¬ UFull (Π H ▹ E))
      → (¬ UFull F) ⊎ (¬ UFull H) × (¬ UFull G) ⊎ (¬ UFull E)
pilem (inj₁ x) = inj₁ (λ x₁ → x (∃Π₁ x₁)) , inj₁ (λ x₁ → x (∃Π₂ x₁))
pilem (inj₂ x) = inj₂ (λ x₁ → x (∃Π₁ x₁)) , inj₂ (λ x₁ → x (∃Π₂ x₁))

pilemΣ :(¬ UFull (Σ F ▹ G)) ⊎ (¬ UFull (Σ H ▹ E))
      → (¬ UFull F) ⊎ (¬ UFull H) × (¬ UFull G) ⊎ (¬ UFull E)
pilemΣ (inj₁ x) = inj₁ (λ x₁ → x (∃Σ₁ x₁)) , inj₁ (λ x₁ → x (∃Σ₂ x₁))
pilemΣ (inj₂ x) = inj₂ (λ x₁ → x (∃Σ₁ x₁)) , inj₂ (λ x₁ → x (∃Σ₂ x₁))

-- If type A does not contain U, then A can be a term of type U.
inverseUniv : ∀ {A} → ¬ (UFull A) → Γ ⊢ A → Γ ⊢ A ∷ U
inverseUniv q (ℕⱼ x) = ℕⱼ x
inverseUniv q (Emptyⱼ x) = Emptyⱼ x
inverseUniv q (Unitⱼ x) = Unitⱼ x
inverseUniv q (Uⱼ x) = ⊥-elim (q ∃U)
inverseUniv q (Πⱼ A ▹ A₁) = Πⱼ inverseUniv (λ x → q (∃Π₁ x)) A ▹ inverseUniv (λ x → q (∃Π₂ x)) A₁
inverseUniv q (Σⱼ A ▹ A₁) = Σⱼ inverseUniv (λ x → q (∃Σ₁ x)) A ▹ inverseUniv (λ x → q (∃Σ₂ x)) A₁
inverseUniv q (univ x) = x

-- If A is a neutral type, then A can be a term of U.
inverseUnivNe : ∀ {A} → Neutral A → Γ ⊢ A → Γ ⊢ A ∷ U
inverseUnivNe neA ⊢A = inverseUniv (noUNe neA) ⊢A

-- Helper function where if at least one type does not contain U, then the
-- equality of types can be an equality of term of type U.
inverseUnivEq′ : ∀ {A B} → (¬ (UFull A)) ⊎ (¬ (UFull B)) → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq′ q (univ x) = x
inverseUnivEq′ q (refl x) = refl (inverseUniv (Sum.id q) x)
inverseUnivEq′ q (sym A≡B) = sym (inverseUnivEq′ (Sum.sym q) A≡B)
inverseUnivEq′ (inj₁ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₁ x) A≡B
      _ , _ , t = syntacticEqTerm w
      y = noU t
  in  trans w (inverseUnivEq′ (inj₁ y) A≡B₁)
inverseUnivEq′ (inj₂ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₂ x) A≡B₁
      _ , t , _ = syntacticEqTerm w
      y = noU t
  in  trans (inverseUnivEq′ (inj₂ y) A≡B) w
inverseUnivEq′ q (Π-cong x A≡B A≡B₁) =
  let w , e = pilem q
  in  Π-cong x (inverseUnivEq′ w A≡B) (inverseUnivEq′ e A≡B₁)
inverseUnivEq′ q (Σ-cong x A≡B A≡B₁) =
  let w , e = pilemΣ q
  in  Σ-cong x (inverseUnivEq′ w A≡B) (inverseUnivEq′ e A≡B₁)

-- If A is a term of U, then the equality of types is an equality of terms of type U.
inverseUnivEq : ∀ {A B} → Γ ⊢ A ∷ U → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq A A≡B = inverseUnivEq′ (inj₁ (noU A)) A≡B
