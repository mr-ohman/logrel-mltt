{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Fundamental.Reducibility {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Reducibility
open import Definition.LogicalRelation.Fundamental

open import Tools.Product


-- Well-formed types are reducible.
reducible : ∀ {A Γ} → Γ ⊢ A → Γ ⊩⟨ ¹ ⟩ A
reducible A = let [Γ] , [A] = fundamental A
              in  reducibleᵛ [Γ] [A]

-- Well-formed equality is reducible.
reducibleEq : ∀ {A B Γ} → Γ ⊢ A ≡ B
            → ∃₂ λ [A] ([B] : Γ ⊩⟨ ¹ ⟩ B) → Γ ⊩⟨ ¹ ⟩ A ≡ B / [A]
reducibleEq {A} {B} A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  reducibleᵛ [Γ] [A]
  ,   reducibleᵛ [Γ] [B]
  ,   reducibleEqᵛ {A} {B} [Γ] [A] [A≡B]

-- Well-formed terms are reducible.
reducibleTerm : ∀ {t A Γ} → Γ ⊢ t ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ∷ A / [A]
reducibleTerm {t} {A} ⊢t =
  let [Γ] , [A] , [t] = fundamentalTerm ⊢t
  in  reducibleᵛ [Γ] [A] , reducibleTermᵛ {t} {A} [Γ] [A] [t]

-- Well-formed term equality is reducible.
reducibleEqTerm : ∀ {t u A Γ} → Γ ⊢ t ≡ u ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A / [A]
reducibleEqTerm {t} {u} {A} t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  reducibleᵛ [Γ] [A] , reducibleEqTermᵛ {t} {u} {A} [Γ] [A] [t≡u]
