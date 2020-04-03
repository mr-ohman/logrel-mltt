{-# OPTIONS --without-K #-}

module Tactic.Substitution where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution

open import Tools.Reflection
open import Tools.List
open import Tools.Unit
open import Tools.Bool
open import Tools.Nat
open import Tools.Product

open import Data.Maybe using (Maybe; just; nothing)


isItA⊩ : ATerm → ATerm → TC ⊤
isItA⊩ hole holeTp@(def (quote _⊩⟨_⟩_) (eqrel ∷ Δ ∷ l ∷ B ∷ [])) with argX B
... | (meta x _) = blockOnMeta x
... | (def (quote subst) (σ ∷ A ∷ [])) = do
  dumpCtx
  -- On goal ↑Δ ⊩⟨ ↑l ⟩ subst ↑σ ↑A the tactic should:
  -- search the context for ↑⊢Δ : ⊢ ↓Δ
  just ⊢Δᵢ ← L.head <$> filterCtx (λ
    { (i , def (quote ⊢_) (Δ′ ∷ [])) → if eq-Arg Δ′ Δ
                                       then just i
                                       else nothing
    ; _ → nothing }) where
      nothing → typeError (
        strErr "Cannot find context validity for :"
        ∷ termErr (argX Δ) ∷ [])
  let ⊢Δ : ATerm
      ⊢Δ = var ⊢Δᵢ []
  -- search the context for all ↑[σ] : ↓Δ ⊩ˢ ↓σ ∷ ↑Γ / _ / ↓⊢Δ
  [σ]ᵢₛ ← filterCtx {A = Nat × Arg ATerm} (λ
    { (i , def (quote _⊩ˢ_∷_/_/_)
               (_ ∷ Δ′ ∷ σ′ ∷ Γ′ ∷ _ ∷ ⊢Δ′ ∷ [])) →
         if (eq-Arg Δ′ Δ) ∧ (eq-Arg σ′ σ) ∧ (eq-Term (argX ⊢Δ′) ⊢Δ)
         then just (i , Γ′)
         else nothing
    ; _ → nothing })
  mapM (λ ([σ]ᵢ , Γ) → do
    dbg (strErr "found ⊩ˢ :" ∷ termErr (argX Γ) ∷ [])
    -- foreach Γ:
    -- search the context for ↑[A] : ↓Γ ⊩ᵛ⟨ ↓l ⟩ ↓A
    just [A]ᵢ ← L.head <$> filterCtxM {A = Nat} (λ
      { (i , def (quote _⊩ᵛ⟨_⟩_/_)
                 args@(_ ∷ Γ′ ∷ _ ∷ A′ ∷ _ ∷ [])) →
          dbg (strErr "⊩ᵛ" ∷ fmtArgs args) >>= λ _ →
          return (if (eq-ArgX Γ′ Γ) ∧ (eq-ArgX A′ A)
          then just i
          else nothing)
      ; _ → return nothing }) where
        nothing → typeError (
          strErr "Cannot find validity for:"
          ∷ termErr (argX A) ∷ [])
    -- try to unify goal with proj₁ ([A] ⊢Δ [σ])
    let soln = var [A]ᵢ (
                 arg (arg-info visible relevant) (var ⊢Δᵢ [])
                 ∷ arg (arg-info visible relevant) (var [σ]ᵢ [])
                 ∷ [])
        soln = def (quote proj₁) (arg (arg-info visible relevant) soln ∷ [])
    unify hole soln) -- TODO skip further iterations if already unified
                     -- TODO use `apply` from nad's code
    [σ]ᵢₛ
  return tt
  --typeError (strErr "Failed to prove:" ∷ termErr holeTp ∷ [])
... | A′ = typeError (
  strErr "Reducible type is not a subst :"
  ∷ termErr A′
  ∷ [])
isItA⊩ hole (def (quote _⊩⟨_⟩_≡_/_) args@(eqrel ∷ Γ ∷ l ∷ A ∷ B ∷ [Γ] ∷ [])) = do
  dbg (strErr "it is ⊩ _ ≡ _" ∷ fmtArgs args)
  return tt
isItA⊩ hole (def (quote _⊩⟨_⟩_∷_/_) args) = do
  dbg (strErr "it is ⊩ _ ∷ _" ∷ fmtArgs args)
  return tt
isItA⊩ hole (def (quote _⊩⟨_⟩_≡_∷_/_) args@(eqrel ∷ Γ ∷ l ∷ t ∷ u ∷ A ∷ [Γ] ∷ [])) = do
  dbg (strErr "it is ⊩ _ ≡ _ ∷ _" ∷ fmtArgs args)
  return tt
isItA⊩ hole holeTp = typeError (
  strErr "Goal is not a reducibility proof :"
  ∷ termErr holeTp
  ∷ [])

macro
  ⊩Tac : ATerm → TC ⊤
  ⊩Tac hole@(meta x _) = inferType hole >>= isItA⊩ hole
  ⊩Tac _ = typeError (strErr "Grrr!" ∷ [])
