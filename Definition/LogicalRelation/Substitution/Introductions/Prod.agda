{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Prod {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Product
import Tools.PropositionalEquality as PE

prodᵛ : ∀ {F G t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substSΠ {F} {G} {t} BΣ [Γ] [F] (Σᵛ {F} {G} [Γ] [F] [G]) [t])
     → Γ ⊩ᵛ⟨ l ⟩ prod t u ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G]
prodᵛ {F} {G} {t} {u} {Γ} {l} [Γ] [F] [G] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F} {G} [Γ] [F] [G]
      prodt : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            → Δ ⊩⟨ l ⟩ subst σ (prod t u) ∷ subst σ (Σ F ▹ G) / proj₁ ([ΣFG] ⊢Δ [σ])
      prodt {Δ} {σ} ⊢Δ [σ] =
        let ⊩σF = proj₁ ([F] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
            ⊢σt = escapeTerm ⊩σF ⊩σt

            [Gt] : Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ]
            [Gt] = substS {F = F} {G = G} [Γ] [F] [G] [t]
            ⊩σG′ : Δ ⊩⟨ l ⟩ subst σ (G [ t ])
            ⊩σG′ = proj₁ ([Gt] ⊢Δ [σ])
            ⊩σG : Δ ⊩⟨ l ⟩ subst (liftSubst σ) G [ subst σ t ]
            ⊩σG = PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (singleSubstLift G t) ⊩σG′
            ⊩σu′ = proj₁ ([u] ⊢Δ [σ])
            ⊩σu : Δ ⊩⟨ l ⟩ subst σ u ∷ _ / ⊩σG
            ⊩σu = irrelevanceTerm′ (singleSubstLift G t) (irrelevance′ (PE.sym (singleSubstLift G t)) _) ⊩σG ⊩σu′
            ⊢σu : Δ ⊢ subst σ u ∷ subst (liftSubst σ) G [ subst σ t ]
            ⊢σu = escapeTerm ⊩σG ⊩σu
            ⊢prod = prodⱼ (subst (liftSubst σ) G) ⊢σt ⊢σu
        in  Σₜ
          (prod (subst σ t) (subst σ u))
          (idRedTerm:*: ⊢prod)
          prodₙ
          (≅-prod-cong (subst (liftSubst σ) G)
            (escapeTermEq ⊩σF
              (reflEqTerm ⊩σF ⊩σt))
            (escapeTermEq ⊩σG
              (reflEqTerm ⊩σG ⊩σu)))
  in  prodt ⊢Δ [σ]
  ,   (λ {σ} [σ′] [σ≡σ′] → {!!})

fstᵛ : ∀ {F G t Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([ΣFG] : Γ ⊩ᵛ⟨ l ⟩ Σ F ▹ G / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / [ΣFG])
       → Γ ⊩ᵛ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [ΣFG] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  {!!}

sndᵛ : ∀ {F G t Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([ΣFG] : Γ ⊩ᵛ⟨ l ⟩ Σ F ▹ G / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / [ΣFG])
       → Γ ⊩ᵛ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / substSΠ {F} {G} {fst t} BΣ [Γ] [F] [ΣFG] (fstᵛ {F} {G} {t} [Γ] [F] [ΣFG] [t])
sndᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [ΣFG] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  {!!}
