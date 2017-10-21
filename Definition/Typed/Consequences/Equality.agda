{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Equality where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.EqView
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reducibility
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
open import Tools.Empty
open import Tools.Unit
import Tools.PropositionalEquality as PE


U≡A′ : ∀ {A Γ l} ([U] : Γ ⊩⟨ l ⟩U)
    → Γ ⊩⟨ l ⟩ U ≡ A / (U-intr [U])
    → A PE.≡ U
U≡A′ (noemb [U]) [U≡A] = [U≡A]
U≡A′ (emb 0<1 [U]) [U≡A] = U≡A′ [U] [U≡A]

-- If A is judgmentally equal to U, then A is propsitionally equal to U.
U≡A : ∀ {A Γ}
    → Γ ⊢ U ≡ A
    → A PE.≡ U
U≡A {A} U≡A with fundamentalEq U≡A
U≡A {A} U≡A | [Γ] , [U] , [A] , [U≡A] =
  let [U]′ = reducible [Γ] [U]
      [U≡A]′ = reducibleEq {U} {A} [Γ] [U] [U≡A]
  in  U≡A′ (U-elim [U]′) (irrelevanceEq [U]′ (U-intr (U-elim [U]′)) [U≡A]′)

ℕ≡A′ : ∀ {A Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
    → Γ ⊩⟨ l ⟩ ℕ ≡ A / (ℕ-intr [ℕ])
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A′ (noemb x) [ℕ≡A] whnfA = whnfRed* [ℕ≡A] whnfA
ℕ≡A′ (emb 0<1 [ℕ]) [ℕ≡A] whnfA = ℕ≡A′ [ℕ] [ℕ≡A] whnfA

-- If A in WHNF is judgmentally equal to ℕ, then A is propsitionally equal to ℕ.
ℕ≡A : ∀ {A Γ}
    → Γ ⊢ ℕ ≡ A
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A {A} ℕ≡A whnfA with fundamentalEq ℕ≡A
ℕ≡A {A} ℕ≡A whnfA | [Γ] , [ℕ] , [A] , [ℕ≡A] =
  let [ℕ]′ = reducible [Γ] [ℕ]
      [ℕ≡A]′ = reducibleEq {ℕ} {A} [Γ] [ℕ] [ℕ≡A]
  in  ℕ≡A′ (ℕ-elim [ℕ]′) (irrelevanceEq [ℕ]′ (ℕ-intr (ℕ-elim [ℕ]′)) [ℕ≡A]′) whnfA

ne≡A′ : ∀ {A K Γ l}
     → ([K] : Γ ⊩⟨ l ⟩ne K)
     → Γ ⊩⟨ l ⟩ K ≡ A / (ne-intr [K])
     → Whnf A
     → ∃ λ M → Neutral M × A PE.≡ M
ne≡A′ (noemb [K]) (ne₌ M D′ neM K≡M) whnfA =
  M , neM , (whnfRed* (red D′) whnfA)
ne≡A′ (emb 0<1 [K]) [K≡A] whnfA = ne≡A′ [K] [K≡A] whnfA

-- If A in WHNF is judgmentally equal to K, then there exists a M such that
-- A is propsitionally equal to M.
ne≡A : ∀ {A K Γ}
    → Neutral K
    → Γ ⊢ K ≡ A
    → Whnf A
    → ∃ λ M → Neutral M × A PE.≡ M
ne≡A {A} neK ne≡A whnfA with fundamentalEq ne≡A
ne≡A {A} neK ne≡A whnfA | [Γ] , [ne] , [A] , [ne≡A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      [ne]′ = proj₁ ([ne] ⊢Γ [id])
      [ne≡A]′ = irrelevanceEq″ {B′ = A} PE.refl (subst-id _)
                                [ne]′ [ne]′ ([ne≡A] ⊢Γ [id])
      neK′ = PE.subst Neutral (PE.sym (subst-id _)) neK
  in  ne≡A′ (ne-elim neK′ [ne]′)
            (irrelevanceEq [ne]′ (ne-intr (ne-elim neK′ [ne]′)) [ne≡A]′) whnfA

Π≡A′ : ∀ {A F G Γ l} ([Π] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
    → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ A / (Π-intr [Π])
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ▹ E
Π≡A′ (noemb [Π]) (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) whnfA =
  F′ , G′ , whnfRed* D′ whnfA
Π≡A′ (emb 0<1 [Π]) [Π≡A] whnfA = Π≡A′ [Π] [Π≡A] whnfA

-- If A is judgmentally equal to Π F ▹ G, then there exists H and E such that
-- A is propsitionally equal to  Π H ▹ E.
Π≡A : ∀ {A F G Γ}
    → Γ ⊢ Π F ▹ G ≡ A
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ▹ E
Π≡A {A} Π≡A whnfA with fundamentalEq Π≡A
Π≡A {A} Π≡A whnfA | [Γ] , [Π] , [A] , [Π≡A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      [Π]′ = proj₁ ([Π] ⊢Γ [id])
      [Π≡A]′ = irrelevanceEq″ {B′ = A} PE.refl (subst-id _)
                               [Π]′ [Π]′ ([Π≡A] ⊢Γ [id])
  in  Π≡A′ (Π-elim [Π]′) (irrelevanceEq [Π]′ (Π-intr (Π-elim [Π]′)) [Π≡A]′) whnfA
