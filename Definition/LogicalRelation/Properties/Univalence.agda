module Definition.LogicalRelation.Properties.Univalence where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance

open import Data.Product
open import Data.Empty


univEq : ∀ {l Γ A} ([U] : Γ ⊩⟨ l ⟩ U) → Γ ⊩⟨ l ⟩ A ∷ U / [U] → Γ ⊩⟨ ⁰ ⟩ A
univEq (U {l< = 0<1} ⊢Γ) (proj₁ , proj₂) = proj₂
univEq (ℕ D) [A] = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
univEq (ne D neK) [A] = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
univEq (Π D ⊢F ⊢G [F] [G] G-ext) [A] = ⊥-elim (U≢Π (whnfRed*' (red D) U))
univEq (emb {l< = 0<1} x) [A] = univEq x [A]

univEqEq : ∀ {l l' Γ A B} ([U] : Γ ⊩⟨ l ⟩ U) ([A] : Γ ⊩⟨ l' ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B ∷ U / [U] → Γ ⊩⟨ l' ⟩ A ≡ B / [A]
univEqEq (U {l< = 0<1} ⊢Γ) [A] U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = proof-irrelevanceEq ⊩t [A] [t≡u]
univEqEq (ℕ D) [A] [A≡B] = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
univEqEq (ne D neK) [A] [A≡B] = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
univEqEq (Π D ⊢F ⊢G [F] [G] G-ext) [A] [A≡B] = ⊥-elim (U≢Π (whnfRed*' (red D) U))
univEqEq (emb {l< = 0<1} x) [A] [A≡B] = univEqEq x [A] [A≡B]
