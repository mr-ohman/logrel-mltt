module Lemma.Completeness where

open import Data.Product

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
import Definition.Typed.Properties as T
open import Definition.LogicalRelation


completeness : ∀ {Γ A} T → Γ ⊢ A → Γ ⊩⟨ T ⟩ A
completeness T A = {!!}

completenessEq : ∀ {Γ A B} T → Γ ⊢ A ≡ B → ∃ λ [A] → Γ ⊩⟨ T ⟩ A ≡ B / [A]
completenessEq T A≡B = {!!}

completenessTerm : ∀ {Γ t A} T → Γ ⊢ t ∷ A → ∃ λ [A] → Γ ⊩⟨ T ⟩ t ∷ A / [A]
completenessTerm T t = {!!}

completenessTermEq : ∀ {Γ A t u} T → Γ ⊢ t ≡ u ∷ A → ∃ λ [A] → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / [A]
completenessTermEq T t≡u = {!!}
