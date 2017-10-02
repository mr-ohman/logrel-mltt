{-# OPTIONS --without-K #-}

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
open import Definition.LogicalRelation.Substitution.Soundness
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE


fullyReducible′ : ∀ {A Γ l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
fullyReducible′ (U′ .⁰ 0<1 ⊢Γ) = U , U , idRed:*: (U ⊢Γ)
fullyReducible′ (ℕ D) = ℕ , ℕ , D
fullyReducible′ (ne′ K D neK K≡K) = K , ne neK , D
fullyReducible′ (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ▹ G , Π , D
fullyReducible′ (emb 0<1 [A]) = fullyReducible′ [A]

fullyReducible : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
fullyReducible a with fundamental a
... | [Γ] , [A] = fullyReducible′ (soundness [Γ] [A])

fullyReducibleTerm′ : ∀ {a A Γ l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
fullyReducibleTerm′ (U x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
fullyReducibleTerm′ (ℕ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
fullyReducibleTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
fullyReducibleTerm′ (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
fullyReducibleTerm′ (emb 0<1 [A]) [a] = fullyReducibleTerm′ [A] [a]

fullyReducibleTerm : ∀ {a A Γ} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
fullyReducibleTerm {a} {A} ⊢a with fundamentalTerm ⊢a
... | [Γ] , [A] , [a] =
  fullyReducibleTerm′ (soundness [Γ] [A]) (soundnessTerm {a} {A} [Γ] [A] [a])
