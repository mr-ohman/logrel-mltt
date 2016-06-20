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
open import Data.Unit

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamentalℕ : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ
  fundamentalℕ ⊢Γ ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ x₂ → id (ℕ ⊢Δ)

  fundamentalU : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ U / valid ⊢Γ
  fundamentalU ⊢Γ ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ x₂ → PE.refl

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) = fundamentalℕ ⊢Γ
  fundamental ⊢Γ (U x) = fundamentalU ⊢Γ
  fundamental ⊢Γ (Π F ▹ G) ⊢Δ [σ] with fundamental ⊢Γ F | fundamental (⊢Γ ∙ F) G
  ... | [F] | [G] = {!!}
  fundamental ⊢Γ (univ x) ⊢Δ [σ] with fundamentalTerm ⊢Γ x
  fundamental ⊢Γ (univ x) ⊢Δ [σ] | [U] , [A] =
    let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
    in [A]₁ , (λ x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x₁))

  fundamentalEq : ∀{Γ A B}  (⊢Γ : ⊢ Γ) → Γ ⊢ A ≡ B
    → ∃₂ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ)
    → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A]
  fundamentalEq ⊢Γ (univ x) with fundamentalTermEq ⊢Γ x
  fundamentalEq ⊢Γ (univ x) | modelsTermEq [A] [t] [u] [t≡u] = {!!} , {!!} , {!!}
  fundamentalEq ⊢Γ (refl D) = let [B] = fundamental ⊢Γ D
                              in  [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (sym A≡B) with fundamentalEq ⊢Γ A≡B
  fundamentalEq ⊢Γ (sym A≡B) | [B] , [A] , [B≡A] = [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq ⊢Γ (trans A≡B₁ B₁≡B) with fundamentalEq ⊢Γ A≡B₁ | fundamentalEq ⊢Γ B₁≡B
  fundamentalEq ⊢Γ (trans A≡B B≡C) | [A] , [B₁] , [A≡B₁] | [B₁]₁ , [B] , [B₁≡B] =
    [A] , [B] , (λ ⊢Δ [σ] → transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) ([A≡B₁] ⊢Δ [σ]) (proof-irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) ([B₁≡B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (Π-cong x A≡B A≡B₁) with fundamentalEq ⊢Γ A≡B | fundamentalEq (⊢Γ ∙ x) A≡B₁
  fundamentalEq ⊢Γ (Π-cong x A≡B A≡B₁) | [F] , [H] , [F≡H] | [G] , [E] , [G≡E] =
    {!!} , {!!} , {!!}

  fundamentalTerm : ∀{Γ A t}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ∷ A →
    ∃ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
  fundamentalTerm ⊢Γ (ℕ x) = fundamentalU ⊢Γ
                           , (λ ⊢Δ [σ] → let ⊢ℕ  = ℕ ⊢Δ
                                             [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                                         in  (⊢ℕ , [ℕ]) , (λ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ]))
  fundamentalTerm ⊢Γ (Π x ▹ x₁) = fundamentalU ⊢Γ , {!!}
  fundamentalTerm ⊢Γ (var x₁ x₂) = {!!}
  fundamentalTerm ⊢Γ (lam x x₁) = {!!}
  fundamentalTerm ⊢Γ (Dt ∘ Du) with fundamentalTerm ⊢Γ Dt | fundamentalTerm ⊢Γ Du
  ... | [ΠAB] , [t] | [A] , [u] = (λ ⊢Δ [σ] → {!!} , {!!}) , {!!}
  fundamentalTerm ⊢Γ (zero x) = fundamentalℕ ⊢Γ , (λ ⊢Δ [σ] → ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ] , (λ x₁ → ℕ≡[ zero , zero , id (zero ⊢Δ) , id (zero ⊢Δ) , refl (zero ⊢Δ) , zero , tt ]))
  fundamentalTerm ⊢Γ (suc n) with fundamentalTerm ⊢Γ n
  fundamentalTerm ⊢Γ (suc n) | [ℕ] , [n] = [ℕ] , {!!}
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
  fundamentalTermEq ⊢Γ (trans t≡u u≡t') with fundamentalTermEq ⊢Γ t≡u | fundamentalTermEq ⊢Γ u≡t'
  fundamentalTermEq ⊢Γ (trans t≡u u≡t') | modelsTermEq [A] [t] [u] [t≡u] | modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ = modelsTermEq [A] [t] {![u]₁!} (λ ⊢Δ [σ] → transEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]) (proof-irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u]₁ ⊢Δ [σ])))
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
  fundamentalTermEq ⊢Γ (natrec-zero F z s) with fundamental (⊢Γ ∙ ℕ ⊢Γ) F | fundamentalTerm ⊢Γ z | fundamentalTerm ⊢Γ s
  fundamentalTermEq ⊢Γ (natrec-zero F₁ z s₁) | [F] | [F₀] , [z] | [s] = modelsTermEq [F₀] {!!} [z] {!!}
  fundamentalTermEq ⊢Γ (natrec-suc x x₁ x₂ x₃) = {!!}
