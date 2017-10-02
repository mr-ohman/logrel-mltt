{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Consistency where

open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.EqView
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Soundness
open import Definition.LogicalRelation.Fundamental


zero≢one'' : ∀ {Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ zero ≡ suc zero ∷ ℕ / ℕ-intr [ℕ] → ⊥
zero≢one'' (noemb x) (ℕₜ₌ .(suc _) .(suc _) d d' k≡k' (suc x₁)) =
  zero≢suc (whnfRed*Term (redₜ d) zero)
zero≢one'' (noemb x) (ℕₜ₌ .zero .zero d d' k≡k' zero) =
  zero≢suc (PE.sym (whnfRed*Term (redₜ d') suc))
zero≢one'' (noemb x) (ℕₜ₌ k k' d d' k≡k' (ne (neNfₜ₌ neK neM k≡m))) =
  zero≢ne neK (whnfRed*Term (redₜ d) zero)
zero≢one'' (emb 0<1 [ℕ]) n = zero≢one'' [ℕ] n

zero≢one' : ∀ {Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ) → Γ ⊩⟨ l ⟩ zero ≡ suc zero ∷ ℕ / [ℕ] → ⊥
zero≢one' [ℕ] [0≡1] =
  zero≢one'' (ℕ-elim [ℕ]) (irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [0≡1])

zero≢one : ∀ {Γ} → Γ ⊢ zero ≡ suc zero ∷ ℕ → ⊥
zero≢one 0≡1 = let [Γ] , modelsTermEq [ℕ] _ _ [0≡1] = fundamentalTermEq 0≡1
           in  zero≢one' (soundness [Γ] [ℕ])
                         (soundnessEqTerm {t = zero} {u = suc zero} {A = ℕ}
                                          [Γ] [ℕ] [0≡1])
