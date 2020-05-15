{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Prod
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Snd

open import Tools.Product
import Tools.PropositionalEquality as PE


Σ-β₁ᵛ : ∀ {F G t u Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t])
      → Γ ⊩ᵛ⟨ l ⟩ fst (prod t u) ≡ t ∷ F / [Γ] / [F]
Σ-β₁ᵛ {F} {G} {t} {u} {Γ} {l} [Γ] [F] [G] [t] [u] =
  let [Gt] = substS {F} {G} {t} [Γ] [F] [G] [t]
      fst⇒t : Γ ⊩ᵛ fst (prod t u) ⇒ t ∷ F / [Γ]
      fst⇒t = (λ {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ ([F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {F = F} {σ = σ} [Γ] ⊢Δ [F] [σ]
                    ⊩σG : Δ ∙ subst σ F ⊩⟨ l ⟩ subst (liftSubst σ) G
                    ⊩σG = proj₁ ([G] (⊢Δ ∙ ⊢σF) [Fσ])
                    ⊢σG = escape ⊩σG

                    ⊩σt = proj₁ ([t] ⊢Δ [σ])
                    ⊢σt = escapeTerm ⊩σF ⊩σt

                    ⊩σGt₁ = proj₁ ([Gt] ⊢Δ [σ])
                    ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

                    ⊩σu₁ = proj₁ ([u] ⊢Δ [σ])
                    ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu₁
                    ⊢σu = escapeTerm ⊩σGt ⊩σu
                in  Σ-β₁ ⊢σF ⊢σG ⊢σt ⊢σu)
  in  proj₂ (redSubstTermᵛ {F} {fst (prod t u)} {t} [Γ] fst⇒t [F] [t])

Σ-β₂ᵛ : ∀ {F G t u Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t])
      → Γ ⊩ᵛ⟨ l ⟩ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ] / [Γ]
          / substS {F} {G} [Γ] [F] [G]
                   (fstᵛ {F} {G} {prod t u} [Γ] [F] [G]
                         (prodᵛ {F} {G} {t} {u} [Γ] [F] [G] [t] [u]))
Σ-β₂ᵛ {F} {G} {t} {u} {Γ} {l} [Γ] [F] [G] [t] [u] =
  let [Gt] = substS {F} {G} {t} [Γ] [F] [G] [t]
      [prod] = prodᵛ {F} {G} {t} {u} [Γ] [F] [G] [t] [u]
      [fst] = fstᵛ {F} {G} {prod t u} [Γ] [F] [G] [prod]
      [Gfst] = substS {F} {G} {fst (prod t u)} [Γ] [F] [G] [fst]
      [fst≡t] = Σ-β₁ᵛ {F} {G} {t} {u} [Γ] [F] [G] [t] [u]
      [Gfst≡Gt] = substSEq {F} {F} {G} {G} {fst (prod t u)} {t}
                           [Γ] [F] [F] (reflᵛ {F} [Γ] [F])
                               [G] [G] (reflᵛ {G} {Γ ∙ F} ([Γ] ∙ [F]) [G])
                               [fst] [t] [fst≡t]

      [u]Gfst = conv₂ᵛ {u} {G [ fst (prod t u) ]} {G [ t ]}
                       [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]

      snd⇒t : Γ ⊩ᵛ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ] / [Γ]
      snd⇒t = (λ {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ ([F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {F = F} {σ = σ} [Γ] ⊢Δ [F] [σ]
                    ⊩σG : Δ ∙ subst σ F ⊩⟨ l ⟩ subst (liftSubst σ) G
                    ⊩σG = proj₁ ([G] (⊢Δ ∙ ⊢σF) [Fσ])
                    ⊢σG = escape ⊩σG

                    ⊩σt = proj₁ ([t] ⊢Δ [σ])
                    ⊢σt = escapeTerm ⊩σF ⊩σt

                    ⊩σGt₁ = proj₁ ([Gt] ⊢Δ [σ])
                    ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

                    ⊩σu₁ = proj₁ ([u] ⊢Δ [σ])
                    ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu₁
                    ⊢σu = escapeTerm ⊩σGt ⊩σu

                    snd⇒t : Δ ⊢ _ ⇒ _ ∷ _
                    snd⇒t = Σ-β₂ ⊢σF ⊢σG ⊢σt ⊢σu
                    σGfst≡σGfst = PE.subst (λ x → Δ ⊢ x ≡ subst σ (G [ fst (prod t u) ]))
                                           (singleSubstLift G (fst (prod t u)))
                                           (refl (escape (proj₁ ([Gfst] ⊢Δ [σ]))))
              in  conv snd⇒t σGfst≡σGfst)
  in  proj₂ (redSubstTermᵛ {G [ fst (prod t u) ]} {snd (prod t u)} {u} [Γ] snd⇒t [Gfst] [u]Gfst)

Σ-ηᵛ : ∀ {F G t Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G])
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ prod (fst t) (snd t) ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G]
Σ-ηᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [G] [t] {Δ} {σ} ⊢Δ [σ] =
  let x = 3
  in  {!!}
