module Definition.LogicalRelation.Properties where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Properties as T
open import Definition.LogicalRelation

open import Data.Product
import Relation.Binary.PropositionalEquality as PE

mutual
  wk : ∀ {Γ Δ A} T → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ T ⟩ A → Δ ⊩⟨ T ⟩ U.wkₜ ρ A
  wk ⁰ ρ ⊢Δ (ℕ x) = ℕ (T.wkRed* ρ ⊢Δ x)
  wk ⁰ ρ ⊢Δ (ne x x₁ x₂) = ne (T.wkRed* ρ ⊢Δ x) (wkNeutral (toWk ρ) x₁) (T.wk ρ ⊢Δ x₂)
  wk ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) = let y = T.wk ρ ⊢Δ x₁ in Π (T.wkRed* ρ ⊢Δ x) y (T.wk (lift ρ) (⊢Δ ∙ y) x₂) (λ ρ₁ ⊢Δ₁ → wk ⁰ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) {!!} {!!}
  wk ¹ ρ ⊢Δ U = U
  wk ¹ ρ ⊢Δ ℕ = ℕ
  wk ¹ ρ ⊢Δ (Π F G A [F] [G] G-ext) = let y = T.wk ρ ⊢Δ F in Π y (T.wk (lift ρ) (⊢Δ ∙ y) G) ([F] ρ ⊢Δ) (λ ρ₁ ⊢Δ₁ → wk ¹ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) {!!} {!!}
  wk ¹ ρ ⊢Δ (emb x) = emb (wk ⁰ ρ ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / [A]
       → Δ ⊩⟨ T ⟩ U.wkₜ ρ A ≡ U.wkₜ ρ B / wk T ρ ⊢Δ [A]
  wkEq ⁰ ρ ⊢Δ (ℕ x) A≡B = T.wkRed* ρ ⊢Δ A≡B
  wkEq ⁰ ρ ⊢Δ (ne x x₁ x₂) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅) = U.wkₜ ρ proj₁ , T.wkRed* ρ ⊢Δ proj₂ , wkNeutral (toWk ρ) proj₃ , T.wk ρ ⊢Δ proj₄ , T.wkEq ρ ⊢Δ proj₅
  wkEq ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆ , proj₇) =
    U.wkₜ ρ proj₁ , wkₜ ρ proj₂ , T.wkEq ρ ⊢Δ proj₃ , wk ⁰ ρ ⊢Δ proj₄ , wk ⁰ ρ ⊢Δ proj₅ , (λ ρ₁ ⊢Δ₁ → wkEq ⁰ ρ₁ ⊢Δ₁ {!wk ⁰ ρ₁ ⊢Δ₁ (Π x x₁ x₂ [F] [G] x₃)!} {!!}) , {!!}
  wkEq ¹ ρ ⊢Δ U A≡B = PE.cong (wkₜ ρ) A≡B
  wkEq ¹ ρ ⊢Δ ℕ A≡B = PE.cong (wkₜ ρ) A≡B
  wkEq ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) A≡B = {!!}
  wkEq ¹ ρ ⊢Δ (emb x) A≡B = wkEq ⁰ ρ ⊢Δ x A≡B

  wkTerm : ∀ {Γ Δ A t} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ∷ A / [A]
         → Δ ⊩⟨ T ⟩ U.wkₜ ρ t ∷ U.wkₜ ρ A / wk T ρ ⊢Δ [A]
  wkTerm ⁰ ρ ⊢Δ (ℕ x) (proj₁ , proj₂ , proj₃) = U.wkₜ ρ proj₁ , T.wkRed*Term ρ ⊢Δ proj₂ , wkNatural (toWk ρ) proj₃
  wkTerm ⁰ ρ ⊢Δ (ne x x₁ x₂) t₁ = T.wkTerm ρ ⊢Δ t₁
  wkTerm ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (λ ρ₁ ⊢Δ₁ [a] a≡b → wkTermEq ⁰ ρ₁ ⊢Δ₁ (wk ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃)) {!!})
  wkTerm ¹ ρ ⊢Δ U (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (wk ⁰ ρ ⊢Δ proj₂)
  wkTerm ¹ ρ ⊢Δ ℕ (proj₁ , proj₂ , proj₃) = U.wkₜ ρ proj₁ , T.wkRed*Term ρ ⊢Δ proj₂ , wkNatural (toWk ρ) proj₃
  wkTerm ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t₁ = {!!}
  wkTerm ¹ ρ ⊢Δ (emb x) t₁ = wkTerm ⁰ ρ ⊢Δ x t₁

  wkTermEq : ∀ {Γ Δ A t u} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / [A]
         → Δ ⊩⟨ T ⟩ U.wkₜ ρ t ≡ U.wkₜ ρ u ∷ U.wkₜ ρ A / wk T ρ ⊢Δ [A]
  wkTermEq ⁰ ρ ⊢Δ (ℕ x) (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) = U.wkₜ ρ proj₁ , U.wkₜ ρ proj₂ , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) proj₃ , T.wkRed*Term ρ ⊢Δ proj₄ , T.wkRed*Term ρ ⊢Δ proj₅ , T.wkEqTerm ρ ⊢Δ proj₆
  wkTermEq ⁰ ρ ⊢Δ (ne x x₁ x₂) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
  wkTermEq ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) t≡u = {!!}
  wkTermEq ¹ ρ ⊢Δ U (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) = T.wkTerm ρ ⊢Δ proj₁ , T.wkTerm ρ ⊢Δ proj₂ , T.wkEqTerm ρ ⊢Δ proj₃ , wk ⁰ ρ ⊢Δ proj₄ , wk ⁰ ρ ⊢Δ proj₅ , wkEq ⁰ ρ ⊢Δ proj₅ proj₆
  wkTermEq ¹ ρ ⊢Δ ℕ (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) = U.wkₜ ρ proj₁ , U.wkₜ ρ proj₂ , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) proj₃ , T.wkRed*Term ρ ⊢Δ proj₄ , T.wkRed*Term ρ ⊢Δ proj₅ , T.wkEqTerm ρ ⊢Δ proj₆
  wkTermEq ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t≡u = {!!}
  wkTermEq ¹ ρ ⊢Δ (emb x) t≡u = wkTermEq ⁰ ρ ⊢Δ x t≡u


proof-irrelevanceEq : ∀ {Γ A B} T (p q : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / p → Γ ⊩⟨ T ⟩ A ≡ B / q
proof-irrelevanceEq T p q A≡B = {!!}
