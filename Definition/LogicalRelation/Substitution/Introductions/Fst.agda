{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Fst {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as Wk hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.Pi

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

fst-subst* : ∀ {F G t t′} → Γ ⊢ F → Γ ∙ F ⊢ G
             → Γ ⊢ t ⇒* t′ ∷ Σ F ▹ G → Γ ⊢ fst t ⇒* fst t′ ∷ F
fst-subst* ⊢F ⊢G (id x) = id (fstⱼ ⊢F ⊢G x)
fst-subst* ⊢F ⊢G (x ⇨ t⇒t′) = fst-subst ⊢F ⊢G x ⇨ fst-subst* ⊢F ⊢G t⇒t′

-- Reducibility of fst with a specific typing derivation
fst′ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst′ {Γ = Γ} {F = F} {t = t} [F] (noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
     (Σₜ p d pProd p≅p [fstp] [sndp]) with
       B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [fstp] : Γ ⊩⟨ _ ⟩ fst p ∷ F / [F]
      [fstp] = irrelevanceTerm′ (wk-id F)
                                ([F'] id (wf ⊢F)) [F]
                                [fstp]
  in  proj₁ (redSubst*Term (fst-subst* ⊢F ⊢G (redₜ d))
                           [F] [fstp])
fst′ {Γ = Γ} {t = t} {l = l} [F] (emb 0<1 x) [t] = fst′ [F] x [t]

-- Reducibility of fst with a general typing derivation
fst″ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst″ {Γ = Γ} {t = t} {l = l} [F] [ΣFG] [t] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
  in  fst′ [F] (Σ-elim [ΣFG]) [t]′

fst-cong′ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong′ {Γ = Γ} {F = F} {G = G} [F]
          [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
          [t≡t′]@(Σₜ₌ p p′ d d′ pProd pProd′ p≅p′ [t] [t′] [fstp] [fstp′] [fst≡] [snd≡]) with
            B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let ⊢Γ = wf ⊢F
      [fstp]₁ = irrelevanceTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fstp]
      [fstp′]₁ = irrelevanceTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fstp′]
      [fst≡]₁ = irrelevanceEqTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fst≡]
      [fstt≡fstp] = proj₂ (redSubst*Term (fst-subst* ⊢F ⊢G (redₜ d)) [F] [fstp]₁)
      [fstt′≡fstp′] = proj₂ (redSubst*Term (fst-subst* ⊢F ⊢G (redₜ d′)) [F] [fstp′]₁)
  in  transEqTerm [F] [fstt≡fstp] (transEqTerm [F] [fst≡]₁ (symEqTerm [F] [fstt′≡fstp′]))
fst-cong′ [F] (emb 0<1 x) = fst-cong′ [F] x

-- Reducibility of congruence of fst
fst-cong″ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong″ {F = F} {G} [F] [ΣFG] [t≡t′] =
  let [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t≡t′]
  in  fst-cong′ [F] (Σ-elim [ΣFG]) [t≡t′]

fst-congᵛ : ∀ {F G t t′ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
          → Γ ⊩ᵛ⟨ l ⟩ fst t ≡ fst t′ ∷ F / [Γ] / [F]
fst-congᵛ {F = F} {G} [Γ] [F] [G] [t] [t′] [t≡t′] ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
  in  fst-cong″ ⊩σF ⊩σΣFG ⊩σt≡t′

-- Validity of first projection
fstᵛ : ∀ {F G t l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
       → Γ ⊩ᵛ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstᵛ {Γ = Γ} {F} {G} {t} {l} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      σfst : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ subst σ (fst t) ∷ subst σ F / proj₁ ([F] ⊢Δ [σ])
      σfst {Δ} {σ} ⊢Δ [σ] =
        let ⊩σF = proj₁ ([F] ⊢Δ [σ])
            ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
        in  fst″ ⊩σF ⊩σΣFG ⊩σt

  in  σfst ⊢Δ [σ] ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let [σF] = proj₁ ([F] ⊢Δ [σ])
            [σΣFG] = proj₁ ([ΣFG] ⊢Δ [σ])
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  fst-cong″ [σF] [σΣFG] [σt≡σ′t])
