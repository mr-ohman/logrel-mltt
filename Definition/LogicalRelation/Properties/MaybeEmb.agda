{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.MaybeEmb {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation


-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A Γ}
         → Γ ⊩⟨ l ⟩ A
         → Γ ⊩⟨ ¹ ⟩ A
maybeEmb {⁰} [A] = emb 0<1 [A]
maybeEmb {¹} [A] = [A]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A Γ}
          → Γ ⊩⟨ ⁰ ⟩ A
          → Γ ⊩⟨ l ⟩ A
maybeEmb′ {⁰} [A] = [A]
maybeEmb′ {¹} [A] = emb 0<1 [A]
