module Lemma.Fundamental where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Context

open import Data.Product

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ x₂ → id (ℕ ⊢Δ)
  fundamental ⊢Γ (U x) ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ x₂ → PE.refl
  fundamental ⊢Γ (Π A ▹ A₁) ⊢Δ [σ] = {!!}
  fundamental ⊢Γ (univ x) ⊢Δ [σ] = {!!}

  fundamentalEq : ∀{Γ A B}  (⊢Γ : ⊢ Γ) → Γ ⊢ A ≡ B
    → ∃₂ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ)
    → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A]
  fundamentalEq ⊢Γ (univ x) = {!!}
  fundamentalEq ⊢Γ (refl D) = let [B] = fundamental ⊢Γ D
                              in  [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (sym A≡B) with fundamentalEq ⊢Γ A≡B
  fundamentalEq ⊢Γ (sym A≡B) | [B] , [A] , [B≡A] = [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq ⊢Γ (trans A≡B A≡B₁) = {!!}
  fundamentalEq ⊢Γ (Π-cong x A≡B A≡B₁) = {!!}

  fundamentalTerm : ∀{Γ A t}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ∷ A →
    ∃ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
  fundamentalTerm ⊢Γ (ℕ x) = {!!}
  fundamentalTerm ⊢Γ (Π x ▹ x₁) = {!!}
  fundamentalTerm ⊢Γ (var x₁ x₂) = {!!}
  fundamentalTerm ⊢Γ (lam x x₁) = {!!}
  fundamentalTerm ⊢Γ (Dt ∘ Du) with fundamentalTerm ⊢Γ Dt | fundamentalTerm ⊢Γ Du
  ... | [ΠAB] , [t] | [A] , [u] = (λ ⊢Δ [σ] → {!!} , {!!}) , {!!}
  fundamentalTerm ⊢Γ (zero x) = {!!}
  fundamentalTerm ⊢Γ (suc x) = {!!}
  fundamentalTerm ⊢Γ (natrec x x₁ x₂ x₃) = {!!}
  fundamentalTerm ⊢Γ (conv t A'≡A) with fundamentalTerm ⊢Γ t | fundamentalEq ⊢Γ A'≡A
  fundamentalTerm ⊢Γ (conv t A'≡A) | [A'] , [t] | [A']₁ , [A] , [A'≡A] =
    [A] , (λ ⊢Δ [σ] → (convTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([A'≡A] ⊢Δ [σ])
                                 (proof-irrelevanceTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                        (proj₁ ([A']₁ ⊢Δ [σ]))
                                                        (proj₁ ([t] ⊢Δ [σ]))))
                    , {!!})

  fundamentalTermEq : ∀{Γ A t t'}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ≡ t' ∷ A → Γ ⊨⟨ ¹ ⟩t t ≡ t' ∷ A / valid ⊢Γ
  fundamentalTermEq ⊢Γ (refl D) with fundamentalTerm ⊢Γ D
  ... | [A] , [t] = modelsTermEq [A] [t] [t] λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
  fundamentalTermEq ⊢Γ (sym D) with fundamentalTermEq ⊢Γ D
  fundamentalTermEq ⊢Γ (sym D) | modelsTermEq [A] [t'] [t] [t'≡t] = modelsTermEq [A] [t] [t'] λ ⊢Δ [σ] →
      symEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t'≡t] ⊢Δ [σ])
  fundamentalTermEq ⊢Γ (trans x x₁) = {!!}
  fundamentalTermEq ⊢Γ (conv t≡u A'≡A) with fundamentalTermEq ⊢Γ t≡u | fundamentalEq ⊢Γ A'≡A
  fundamentalTermEq ⊢Γ (conv t≡u A'≡A) | modelsTermEq [A'] [t] [u] [t≡u] | [A']₁ , [A] , [A'≡A] =
    modelsTermEq [A] {!!} {!!}
                 (λ ⊢Δ [σ] → convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([A'≡A] ⊢Δ [σ])
                                         (proof-irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                                  (proj₁ ([A']₁ ⊢Δ [σ]))
                                                                  ([t≡u] ⊢Δ [σ])))
  fundamentalTermEq ⊢Γ (Π-cong x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (app-cong x x₁) = {!!}
  fundamentalTermEq ⊢Γ (β-red x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (fun-ext x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (suc-cong x) = {!!}
  fundamentalTermEq ⊢Γ (natrec-cong x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (natrec-zero x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (natrec-suc x x₁ x₂ x₃) = {!!}
