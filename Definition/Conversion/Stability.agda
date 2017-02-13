module Definition.Conversion.Stability where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Substitution

open import Tools.Unit
open import Tools.Product
import Tools.PropositionalEquality as PE


data ⊢_≡_ : (Γ Δ : Con Term) → Set where
  ε : ⊢ ε ≡ ε
  _∙_ : ∀ {Γ Δ A B} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Δ ∙ B

reflConEq : ∀ {Γ} → ⊢ Γ → ⊢ Γ ≡ Γ
reflConEq ε = ε
reflConEq (⊢Γ ∙ ⊢A) = reflConEq ⊢Γ ∙ refl ⊢A

mutual
  substx : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → Δ ⊢ₛ idSubst ∷ Γ
  substx ε = [ ε , ε , tt ]
  substx (_∙_ {Γ} {Δ} {A} {B} Γ≡Δ A≡B) =
    let [ ⊢Γ , ⊢Δ , [σ] ] = substx Γ≡Δ
        ⊢A , ⊢B = syntacticEq A≡B
        Δ⊢B = stability Γ≡Δ ⊢B
    in  [ ⊢Γ ∙ ⊢A , ⊢Δ ∙ Δ⊢B
        , (wk1Subst' ⊢Γ ⊢Δ Δ⊢B [σ]
        , conv (var (⊢Δ ∙ Δ⊢B) here)
               (PE.subst (λ x → _ ⊢ _ ≡ x)
                         (PE.trans (PE.sym (idSubst-lemma₀ (wk1 A))) (subst-wk A))
                         (wkEq (step id) (⊢Δ ∙ Δ⊢B) (stabilityEq Γ≡Δ (sym A≡B))))) ]

  stability : ∀ {A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A → Δ ⊢ A
  stability Γ≡Δ A =
    let q = substitution A (substx Γ≡Δ)
    in  PE.subst (λ x → _ ⊢ x) (idSubst-lemma₀ _) q

  stabilityEq : ∀ {A B Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → Δ ⊢ A ≡ B
  stabilityEq Γ≡Δ A≡B =
    let q = substitutionEq A≡B (substx Γ≡Δ)
    in  PE.subst₂ (λ x y → _ ⊢ x ≡ y) (idSubst-lemma₀ _) (idSubst-lemma₀ _) q

symConEq : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → ⊢ Δ ≡ Γ
symConEq ε = ε
symConEq (Γ≡Δ ∙ A≡B) = symConEq Γ≡Δ ∙ stabilityEq Γ≡Δ (sym A≡B)

stabilityTerm : ∀ {t A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
stabilityTerm Γ≡Δ t =
  let q = substitutionTerm t (substx Γ≡Δ)
  in  PE.subst₂ (λ x y → _ ⊢ x ∷ y) (idSubst-lemma₀ _) (idSubst-lemma₀ _) q

-- Cannot solve
-- stabilityVar : ∀ {x A Γ Δ} → ⊢ Γ ≡ Δ → x ∷ A ∈ Γ → x ∷ A ∈ Δ
-- stabilityVar (Γ≡Δ ∙ A≡B) here = {!!}
-- stabilityVar (Γ≡Δ ∙ A≡B) (there x) = there (stabilityVar Γ≡Δ x)

stabilityRedTerm : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ t ⇒ u ∷ A
stabilityRedTerm Γ≡Δ (conv d x) =
  conv (stabilityRedTerm Γ≡Δ d) (stabilityEq Γ≡Δ x)
stabilityRedTerm Γ≡Δ (app-subst d x) =
  app-subst (stabilityRedTerm Γ≡Δ d) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (β-red x x₁ x₂) =
  β-red (stability Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl x) x₁)
        (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-subst x x₁ x₂ d) =
  let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
  in  natrec-subst (stability (Γ≡Δ ∙ refl (ℕ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                   (stabilityTerm Γ≡Δ x₂) (stabilityRedTerm Γ≡Δ d)
stabilityRedTerm Γ≡Δ (natrec-zero x x₁ x₂) =
  let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
  in  natrec-zero (stability (Γ≡Δ ∙ refl (ℕ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                  (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-suc x x₁ x₂ x₃) =
  let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
  in  natrec-suc (stabilityTerm Γ≡Δ x) (stability (Γ≡Δ ∙ refl (ℕ ⊢Γ)) x₁)
                 (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)

stabilityRed : ∀ {A B Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒ B → Δ ⊢ A ⇒ B
stabilityRed Γ≡Δ (univ x) = univ (stabilityRedTerm Γ≡Δ x)

stabilityRed* : ∀ {A B Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒* B → Δ ⊢ A ⇒* B
stabilityRed* Γ≡Δ (id x) = id (stability Γ≡Δ x)
stabilityRed* Γ≡Δ (x ⇨ D) = stabilityRed Γ≡Δ x ⇨ stabilityRed* Γ≡Δ D

stabilityRed*Term : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ t ⇒* u ∷ A
stabilityRed*Term Γ≡Δ (id x) = id (stabilityTerm Γ≡Δ x)
stabilityRed*Term Γ≡Δ (x ⇨ d) = stabilityRedTerm Γ≡Δ x ⇨ stabilityRed*Term Γ≡Δ d

mutual
  stability~↑ : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑ A
              → Δ ⊢ k ~ l ↑ A
  stability~↑ Γ≡Δ (var x) =
    var (stabilityTerm Γ≡Δ x)
  stability~↑ Γ≡Δ (app k~l x) =
    app (stability~↓ Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑ Γ≡Δ (natrec x₁ x₂ x₃ k~l) =
    let [ ⊢Γ , _ , _ ] = substx Γ≡Δ
    in natrec (stabilityConv↑ (Γ≡Δ ∙ (refl (ℕ ⊢Γ))) x₁)
              (stabilityConv↑Term Γ≡Δ x₂)
              (stabilityConv↑Term Γ≡Δ x₃)
              (stability~↓ Γ≡Δ k~l)

  stability~↓ : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓ A
              → Δ ⊢ k ~ l ↓ A
  stability~↓ Γ≡Δ ([~] A D whnfA k~l) =
    [~] A (stabilityRed* Γ≡Δ D) whnfA (stability~↑ Γ≡Δ k~l)

  stabilityConv↑ : ∀ {A B Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↑] B
                 → Δ ⊢ A [conv↑] B
  stabilityConv↑ Γ≡Δ ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    [↑] A' B' (stabilityRed* Γ≡Δ D) (stabilityRed* Γ≡Δ D') whnfA' whnfB'
        (stabilityConv↓ Γ≡Δ A'<>B')

  stabilityConv↓ : ∀ {A B Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↓] B
                 → Δ ⊢ A [conv↓] B
  stabilityConv↓ Γ≡Δ (U-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  U-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (ℕ-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (ne x) =
    ne (stability~↓ Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (Π-cong F A<>B A<>B₁) =
    Π-cong (stability Γ≡Δ F) (stabilityConv↑ Γ≡Δ A<>B)
           (stabilityConv↑ (Γ≡Δ ∙ refl F) A<>B₁)

  stabilityConv↑Term : ∀ {t u A Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↑] u ∷ A
                     → Δ ⊢ t [conv↑] u ∷ A
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u) =
    [↑]ₜ B t' u' (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d)
                 (stabilityRed*Term Γ≡Δ d') whnfB whnft' whnfu'
                 (stabilityConv↓Term Γ≡Δ t<>u)

  stabilityConv↓Term : ∀ {t u A Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷ A
                     → Δ ⊢ t [conv↓] u ∷ A
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) =
    ne-ins (stabilityTerm Γ≡Δ t) (stabilityTerm Γ≡Δ u) neN (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (fun-ext F x x₁ y y₁ t<>u) =
    fun-ext (stability Γ≡Δ F) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
            y y₁ (stabilityConv↑Term (Γ≡Δ ∙ refl F) t<>u)
