{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Reducibility
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A Γ l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm′ (U′ .⁰ 0<1 ⊢Γ) = U , U , idRed:*: (U ⊢Γ)
whNorm′ (ℕ D) = ℕ , ℕ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ▹ G , Π , D
whNorm′ (emb 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm a with fundamental a
... | [Γ] , [A] = whNorm′ (reducible [Γ] [A])

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A Γ l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm′ (U x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb 0<1 [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A Γ} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm {a} {A} ⊢a with fundamentalTerm ⊢a
... | [Γ] , [A] , [a] =
  whNormTerm′ (reducible [Γ] [A]) (reducibleTerm {a} {A} [Γ] [A] [a])
