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
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t])
     → Γ ⊩ᵛ⟨ l ⟩ prod t u ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G]
prodᵛ {F} {G} {t} {u} {Γ} {l} [Γ] [F] [G] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [Gt] = substS {F} {G} [Γ] [F] [G] [t]
      [ΣFG] = Σᵛ {F} {G} [Γ] [F] [G]

      σprod : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → Δ ⊩⟨ l ⟩ subst σ (prod t u) ∷ subst σ (Σ F ▹ G) / proj₁ ([ΣFG] ⊢Δ [σ])
      σprod {Δ} {σ} ⊢Δ [σ] =
        let ⊩σF = proj₁ ([F] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
            ⊩σGt′ : Δ ⊩⟨ l ⟩ subst σ (G [ t ])
            ⊩σGt′ = proj₁ ([Gt] ⊢Δ [σ])
            ⊩σGt : Δ ⊩⟨ l ⟩ subst (liftSubst σ) G [ subst σ t ]
            ⊩σGt = PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (singleSubstLift G t) ⊩σGt′
            ⊩σu′ = proj₁ ([u] ⊢Δ [σ])
            ⊩σu : Δ ⊩⟨ l ⟩ subst σ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σGt
            ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt ⊩σu′
        in  Σₜ (prod (subst σ t) (subst σ u))
               (idRedTerm:*: (prodⱼ (subst (liftSubst σ) G)
                 (escapeTerm ⊩σF ⊩σt)
                 (escapeTerm ⊩σGt ⊩σu)))
               prodₙ
               (≅-prod-cong (subst (liftSubst σ) G)
                 (escapeTermEq ⊩σF
                   (reflEqTerm ⊩σF ⊩σt))
                 (escapeTermEq ⊩σGt
                   (reflEqTerm ⊩σGt ⊩σu)))
               (λ {ρ} {E} [ρ] ⊢E →
                 let ⊩ρσF = wk [ρ] ⊢E ⊩σF
                     ⊩ρσt : E ⊩⟨ l ⟩ U.wk ρ (subst σ t) ∷ U.wk ρ (subst σ F) / ⊩ρσF
                     ⊩ρσt = wkTerm [ρ] ⊢E ⊩σF ⊩σt
                     ⊩ρσGt = wk [ρ] ⊢E ⊩σGt′
                     ⊩ρσu = wkTerm [ρ] ⊢E ⊩σGt′ ⊩σu′
                     bla = escapeTerm ⊩ρσGt ⊩ρσu
                     d : E ⊢ fst (U.wk ρ (subst σ (prod t u))) ⇒ U.wk ρ (subst σ t) ∷ U.wk ρ (subst σ F)
                     d = Σ-β₁ (U.wk (lift ρ) (subst (liftSubst σ) G))
                       (escapeTerm ⊩ρσF ⊩ρσt)
                         (PE.subst (λ x → E ⊢ U.wk ρ (subst σ u) ∷ x)
                           (PE.begin
                              U.wk ρ (subst σ (G [ t ]))
                            PE.≡⟨ PE.cong (U.wk ρ) (singleSubstLift G t) ⟩
                              U.wk ρ ((subst (liftSubst σ) G) [ subst σ t ])
                            PE.≡⟨ wk-β (subst (liftSubst σ) G) ⟩
                              U.wk (lift ρ) (subst (liftSubst σ) G) [ U.wk ρ (subst σ t) ]
                            PE.∎)
                            bla)
                     d2 : E ⊢ snd (U.wk ρ (subst σ (prod t u))) ⇒ U.wk ρ (subst σ u) ∷ U.wk (lift ρ) (subst σ G) [ _ ]
                     d2 = {!!}
                     [fst] = proj₁ (redSubstTerm d ⊩ρσF ⊩ρσt)
                     [snd] = proj₁ (redSubstTerm {!!} ⊩ρσGt ⊩ρσu)
                 in  [fst] ,
                     {!!})
  in  σprod ⊢Δ [σ] ,
      (λ {σ′} [σ′] [σ≡σ′] →
    let ⊩σΣ = proj₁ ([ΣFG] ⊢Δ [σ])
        ⊩σ′Σ = proj₁ ([ΣFG] ⊢Δ [σ′])
        ⊩σprod = σprod ⊢Δ [σ]
        σΣ≡σ′Σ : Δ ⊩⟨ l ⟩ subst σ (Σ F ▹ G) ≡ subst σ′ (Σ F ▹ G) / ⊩σΣ
        σΣ≡σ′Σ = proj₂ ([ΣFG] ⊢Δ [σ]) [σ′] [σ≡σ′]
        ⊩σ′prod : Δ ⊩⟨ l ⟩ prod (subst σ′ t) (subst σ′ u) ∷ subst σ (Σ F ▹ G) / ⊩σΣ
        ⊩σ′prod = convTerm₂ ⊩σΣ ⊩σ′Σ σΣ≡σ′Σ (σprod ⊢Δ [σ′])
        ⊩σG′ : Δ ⊩⟨ l ⟩ subst σ (G [ t ])
        ⊩σG′ = proj₁ ([Gt] ⊢Δ [σ])
        ⊩σG : Δ ⊩⟨ l ⟩ subst (liftSubst σ) G [ subst σ t ]
        ⊩σG = PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (singleSubstLift G t) ⊩σG′
        σu≡σ′u : Δ ⊩⟨ l ⟩ subst σ u ≡ subst σ′ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σG
        σu≡σ′u = irrelevanceEqTerm′ (singleSubstLift G t) ⊩σG′ ⊩σG (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])
    in Σₜ₌ (subst σ (prod t u))
           (subst σ′ (prod t u))
           (idRedTerm:*: (escapeTerm ⊩σΣ ⊩σprod))
           (idRedTerm:*: (escapeTerm ⊩σΣ ⊩σ′prod))
           prodₙ
           prodₙ
           (≅-prod-cong (subst (liftSubst σ) G)
             (escapeTermEq (proj₁ ([F] ⊢Δ [σ]))
               (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]))
             (escapeTermEq ⊩σG σu≡σ′u))
           ⊩σprod
           ⊩σ′prod)

-- Reducibility of fst with a specific typing derivation
fst′ : ∀ {F G t Γ l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst′ {F = F} {t = t} {Γ = Γ} [F] (noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
     (Σₜ p d pProd p≅p pElim) with
       proj₁ (B-PE-injectivity BΣ (whnfRed* (red D) Σₙ))
     | proj₂ (B-PE-injectivity BΣ (whnfRed* (red D) Σₙ))
... | PE.refl | PE.refl =
  let [fst] = λ {ρ} {Δ} [ρ] ⊢Δ → proj₁ (pElim {ρ} {Δ} [ρ] ⊢Δ)
      ⊩fstp : Γ ⊩⟨ _ ⟩ fst p ∷ F / [F]
      ⊩fstp = irrelevanceTerm″
        (wk-id _) (PE.cong fst (wk-id p))
        ([F'] id (wf ⊢F)) [F]
        ([fst] id (wf ⊢F))
  in  proj₁ (redSubst*Term
    (fst-subst* (redₜ d))
    [F]
    ⊩fstp)
fst′ {t = t} {Γ = Γ} {l = l} [F] (emb 0<1 x) [t] = fst′ [F] x [t]

-- Reducibility of fst with a general typing derivation
fst″ : ∀ {F G t Γ l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst″ {t = t} {Γ = Γ} {l = l} [F] [ΣFG] [t] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
  in  fst′ [F] (Σ-elim [ΣFG]) [t]′

fst-cong′ : ∀ {F G t t′ Γ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong′ {F = F} {G = G} {Γ = Γ} [F]
          [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
          [t≡t′]@(Σₜ₌ q q′ d d′ qProd qProd′ q≅q′ [t] [t′]) with
            B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [fstt] = fst′ [F] [ΣFG] [t]
      [fstt′] = fst′ [F] [ΣFG] [t′]
      [q] : Γ ⊩⟨ _ ⟩ q ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
      [q] = {!!}
      [q′] : Γ ⊩⟨ _ ⟩ q′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
      [q′] = {!!}
      a = 3
  in  {!!}
fst-cong′ [F] (emb 0<1 x) = fst-cong′ [F] x

-- Reducibility of congruence of fst
fst-cong″ : ∀ {F G t t′ Γ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
            ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
            ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σ F ▹ G / [ΣFG])
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong″ {F} {G} [F] [ΣFG] [t] [t′] [t≡t′] =
  let [t] = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
      [t′] = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t′]
      [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t≡t′]
  in  fst-cong′ [F] (Σ-elim [ΣFG]) [t≡t′]

-- Validity of first projection
fstᵛ : ∀ {F G t Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G])
       → Γ ⊩ᵛ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F} {G} [Γ] [F] [G]
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
            [σ′ΣFG] = proj₁ ([ΣFG] ⊢Δ [σ′])
            [σΣFG≡σ′ΣFG] = proj₂ ([ΣFG] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σt] = proj₁ ([t] ⊢Δ [σ])
            [σ′t] = proj₁ ([t] ⊢Δ [σ′])
            [σ′t] : Δ ⊩⟨ l ⟩ subst σ′ t ∷ subst σ (Σ F ▹ G) / [σΣFG]
            [σ′t] = convTerm₂ [σΣFG] [σ′ΣFG] [σΣFG≡σ′ΣFG] [σ′t]
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  fst-cong″ [σF] [σΣFG] [σt] [σ′t] [σt≡σ′t] )

snd-subst* : ∀ {Γ l l′ F G t t′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ F ▹ G)
             ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ Σ F ▹ G / [ΣFG])
             → Γ ⊢ t ⇒* t′ ∷ Σ F ▹ G
             → Γ ⊢ snd t ⇒* snd t′ ∷ G [ fst t ]
snd-subst* _ _ _ (id x) = id (sndⱼ x)
snd-subst* {Γ = Γ} {F = F} {G = G} {t = t} {t′ = t″} [F] [ΣFG] [t″] t⇒*t″@(_⇨_ {t′ = t′} t⇒t′ t′⇒*t″) =
  let [t] , _ = redSubst*Term t⇒*t″ [ΣFG] [t″]
      [t′] , _ = redSubst*Term t′⇒*t″ [ΣFG] [t″]
      [t≡t′] : Γ ⊩⟨ _ ⟩ t ≡ t′ ∷ Σ F ▹ G / [ΣFG]
      [t≡t′] = proj₂ (redSubstTerm t⇒t′ [ΣFG] [t′])
      [fstt] : Γ ⊩⟨ _ ⟩ fst t ∷ F / [F]
      [fstt] = fst″ [F] [ΣFG] [t]
      [fstt′] : Γ ⊩⟨ _ ⟩ fst t′ ∷ F / [F]
      [fstt′] = fst″ [F] [ΣFG] [t′]
      [Gfstt] : Γ ⊩⟨ _ ⟩ G [ fst t ]
      [Gfstt] = substSΠ₁ BΣ [ΣFG] [F] [fstt]
      [Gfstt′] : Γ ⊩⟨ _ ⟩ G [ fst t′ ]
      [Gfstt′] = substSΠ₁ BΣ [ΣFG] [F] [fstt′]
      [fstt′≡fstt] : Γ ⊩⟨ _ ⟩ fst t′ ≡ fst t ∷ F / [F]
      [fstt′≡fstt] = symEqTerm [F] (fst-cong″ [F] [ΣFG] [t] [t′] [t≡t′])
      [Gfstt′≡Gfstt] : Γ ⊩⟨ _ ⟩ G [ fst t′ ] ≡ G [ fst t ] / [Gfstt′]
      [Gfstt′≡Gfstt] = substSΠ₂ BΣ [ΣFG] (reflEq [ΣFG]) [F] [F] [fstt′] [fstt] [fstt′≡fstt] [Gfstt′] [Gfstt]
  in  snd-subst t⇒t′ ⇨ conv*
                         (snd-subst* [F] [ΣFG] [t″] t′⇒*t″)
                         (≅-eq (escapeEq [Gfstt′] [Gfstt′≡Gfstt]))

snd′ : ∀ {F G t Γ l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
       → Γ ⊩⟨ l′ ⟩ snd t ∷ G [ fst t ] / [Gfst]
snd′ {F = F} {G = G} {t = t} {Γ = Γ} {l = l} {l′ = l′} [F]
     [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
     [t]@(Σₜ p d pProd p≅p pElim) [Gfst] with
       B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [fst] = λ {ρ} {Δ} [ρ] ⊢Δ → proj₁ (pElim {ρ} {Δ} [ρ] ⊢Δ)
      [snd] = λ {ρ} {Δ} [ρ] ⊢Δ → proj₂ (pElim {ρ} {Δ} [ρ] ⊢Δ)

      wkidGfstp≡Gfstp = (PE.begin
               (U.wk (lift id) G) [ fst (U.wk id p) ]
             PE.≡⟨ PE.cong (λ x → x [ fst (U.wk id p) ]) (wk-lift-id G) ⟩
               G [ fst (U.wk id p) ]
             PE.≡⟨ PE.cong (λ x → G [ fst x ]) (wk-id p) ⟩
               G [ fst p ]
             PE.∎)

      [p] : Γ ⊩⟨ _ ⟩ p ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
      [p] = Σₜ p (idRedTerm:*: (⊢u-redₜ d)) pProd p≅p pElim
      _ , [t≡p] = redSubst*Term (redₜ d) (B-intr BΣ [ΣFG]) [p]

      [fstt] = fst″ [F] (B-intr BΣ [ΣFG]) [t]
      [fstp] = fst″ [F] (B-intr BΣ [ΣFG]) [p]

      [fstt≡fstp] = fst-cong″ [F] (B-intr BΣ [ΣFG]) [t] [p] [t≡p]

      [Gfstt] = substSΠ₁ BΣ (B-intr BΣ [ΣFG]) [F] [fstt]
      [Gfstp] = substSΠ₁ BΣ (B-intr BΣ [ΣFG]) [F] [fstp]

      [Gfstt≡Gfstp] : Γ ⊩⟨ l ⟩ G [ fst t ] ≡ G [ fst p ] / [Gfstt]
      [Gfstt≡Gfstp] = substSΠ₂ BΣ (B-intr BΣ [ΣFG]) (reflEq (B-intr BΣ [ΣFG])) [F] [F] [fstt] [fstp] [fstt≡fstp] [Gfstt] [Gfstp]

      [sndp] : Γ ⊩⟨ l ⟩ snd p ∷ G [ fst p ] / [Gfstp]
      [sndp] = irrelevanceTerm″
        wkidGfstp≡Gfstp (PE.cong snd (wk-id p))
        ([G'] id (wf ⊢F) ([fst] id (wf ⊢F))) [Gfstp]
        ([snd] id (wf ⊢F))

      [sndp] : Γ ⊩⟨ l ⟩ snd p ∷ G [ fst t ] / [Gfstt]
      [sndp] = convTerm₂ [Gfstt] [Gfstp] [Gfstt≡Gfstp] [sndp]

      [sndp] : Γ ⊩⟨ l′ ⟩ snd p ∷ G [ fst t ] / [Gfst]
      [sndp] = irrelevanceTerm [Gfstt] [Gfst] [sndp]

  in  proj₁ (redSubst*Term
              (snd-subst* [F] (B-intr BΣ [ΣFG]) [p] (redₜ d))
              [Gfst]
              [sndp])

snd′ [F] (emb 0<1 x) = snd′ [F] x

snd″ : ∀ {F G t Γ l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
       → Γ ⊩⟨ l′ ⟩ snd t ∷ G [ fst t ] / [Gfst]
snd″ {t = t} {Γ = Γ} {l = l} [F] [ΣFG] [t] [Gfst] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
  in  snd′ [F] (Σ-elim [ΣFG]) [t]′ [Gfst]

-- Validity of second projection
sndᵛ : ∀ {F G t Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G])
       → Γ ⊩ᵛ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / substS {F} {G} [Γ] [F] [G] (fstᵛ {F} {G} {t} [Γ] [F] [G] [t])
sndᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F} {G} [Γ] [F] [G]
      [Gfst] : Γ ⊩ᵛ⟨ l ⟩ G [ fst t ] / [Γ]
      [Gfst] = substS {F} {G} [Γ] [F] [G] (fstᵛ {F} {G} {t} [Γ] [F] [G] [t])

      σsnd : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ subst σ (snd t) ∷ subst σ (G [ fst t ]) / proj₁ ([Gfst] ⊢Δ [σ])
      σsnd {Δ} {σ} ⊢Δ [σ] =
        let ⊩σF = proj₁ ([F] ⊢Δ [σ])
            ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
            ⊩σGfstt = proj₁ ([Gfst] ⊢Δ [σ])
            ⊩σGfstt′ = PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (singleSubstLift G (fst t)) ⊩σGfstt
            ⊩σsnd = snd″ ⊩σF ⊩σΣFG ⊩σt ⊩σGfstt′
        in  irrelevanceTerm′
              (PE.sym (singleSubstLift G (fst t)))
              ⊩σGfstt′  ⊩σGfstt
              ⊩σsnd
  in  σsnd ⊢Δ [σ] ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let [σF] = proj₁ ([F] ⊢Δ [σ])
            [σΣFG] = proj₁ ([ΣFG] ⊢Δ [σ])
            [σ′ΣFG] = proj₁ ([ΣFG] ⊢Δ [σ′])
            [σΣFG≡σ′ΣFG] = proj₂ ([ΣFG] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σt] = proj₁ ([t] ⊢Δ [σ])
            [σ′t] = proj₁ ([t] ⊢Δ [σ′])
            [σ′t] : Δ ⊩⟨ l ⟩ subst σ′ t ∷ subst σ (Σ F ▹ G) / [σΣFG]
            [σ′t] = convTerm₂ [σΣFG] [σ′ΣFG] [σΣFG≡σ′ΣFG] [σ′t]
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  {!!})

