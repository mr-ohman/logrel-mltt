module Lemma.Completeness where

open import Data.Product
import Relation.Binary.PropositionalEquality as PE

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
import Definition.Typed.Properties as T
open import Definition.LogicalRelation


completeness : ∀ {Γ A} → Γ ⊢ A → Γ ⊩¹ A
completeness (ℕ x) = ℕ
completeness (U x) = U
completeness (Π A ▹ A₁) = Π A A₁ (completeness A) {!!} {!!} {!!}
completeness (univ x) = emb {!!}

completenessEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ∃ λ [A] → Γ ⊩¹ A ≡ B / [A]
completenessEq (univ x) = {!!}
completenessEq (refl x) = {!!}
completenessEq (sym A≡B) = {!!}
completenessEq (trans A≡B A≡B₁) = {!!}
completenessEq (Π-cong x A≡B A≡B₁) = {!!}

completenessTerm : ∀ {Γ t A} → Γ ⊢ t ∷ A → ∃ λ [A] → Γ ⊩¹ t ∷ A / [A]
completenessTerm t = {!!}

completenessTermEq : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → ∃ λ [A] → Γ ⊩¹ t ≡ u ∷ A / [A]
completenessTermEq t≡u = {!!}
