{-# OPTIONS --without-K --allow-unsolved-metas #-}

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
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Fst

open import Tools.Product
import Tools.PropositionalEquality as PE

prod′ : ∀ {F G t u Γ l l′ l″}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l″ ⟩ G [ t ])
       ([u] : Γ ⊩⟨ l″ ⟩ u ∷ G [ t ] / [Gt])
       ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ ⟩ Σ F ▹ G)
     → Γ ⊩⟨ l′ ⟩ prod t u ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
prod′ {F} {G} {t} {u} {Γ} {l} {l′} {l″} [F] [t] [Gt] [u]
      [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext)) with
        B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let ⊢t = escapeTerm [F] [t]
      ⊢u = escapeTerm [Gt] [u]
      ⊢Γ = wf ⊢F

      fst⇒t : Γ ⊢ fst (prod t u) ⇒ t ∷ F
      fst⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u
      [fstprod] , [fstprod≡t] = redSubstTerm fst⇒t [F] [t]
      [fstprod]′ = (irrelevanceTerm′ (PE.sym (wk-id F))
                                     [F] ([F]₁ id ⊢Γ)
                                     [fstprod])

      wkLiftIdEq = PE.cong (λ x → x [ fst (prod t u ) ]) (wk-lift-id G)
      [Gfst] = [G]₁ id ⊢Γ [fstprod]′
      [Gfst]′ = irrelevance′ wkLiftIdEq [Gfst]

      [t]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                              [F] ([F]₁ id ⊢Γ)
                              [t]
      [fstprod≡t]′ = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                        [F] ([F]₁ id ⊢Γ)
                                        [fstprod≡t]

      [Gfst≡Gt] = irrelevanceEq″ wkLiftIdEq (PE.cong (λ x → x [ t ]) (wk-lift-id G))
                                 [Gfst] [Gfst]′
                                 (G-ext id ⊢Γ [fstprod]′ [t]′ [fstprod≡t]′)
      [u]′ = convTerm₂ [Gfst]′ [Gt] [Gfst≡Gt] [u]

      snd⇒u : Γ ⊢ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ]
      snd⇒u = Σ-β₂ ⊢F ⊢G ⊢t ⊢u
      [sndprod] = proj₁ (redSubstTerm snd⇒u [Gfst]′ [u]′)
  in  Σₜ (prod t u)
         (idRedTerm:*: (prodⱼ ⊢F ⊢G ⊢t ⊢u))
         prodₙ
         (≅-prod-cong ⊢F ⊢G
                      (escapeTermEq [F] (reflEqTerm [F] [t]))
                      (escapeTermEq [Gt] (reflEqTerm [Gt] [u])))
         [fstprod]′
         (irrelevanceTerm′ (PE.sym wkLiftIdEq)
                       [Gfst]′ [Gfst]
                       [sndprod])
prod′ {F} {G} {t} {u} {Γ} {l} {l′} [F] [t] [Gt] [u]
      [ΣFG]@(emb 0<1 x) = prod′ [F] [t] [Gt] [u] x

prod″ : ∀ {F G t u Γ l l′}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
       ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
       ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ F ▹ G)
     → Γ ⊩⟨ l′ ⟩ prod t u ∷ Σ F ▹ G / [ΣFG]
prod″ [F] [t] [Gt] [u] [ΣFG] =
      let [prod] = prod′ [F] [t] [Gt] [u] (B-elim BΣ [ΣFG])
      in  irrelevanceTerm (B-intr BΣ (B-elim BΣ [ΣFG])) [ΣFG] [prod]

prod-cong′ : ∀ {F G t t′ u u′ Γ l l′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
             ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ F / [F])
             ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ F / [F])
             ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
             ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ] / [Gt])
             ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Gt])
             ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ ⟩ Σ F ▹ G)
             → Γ ⊩⟨ l′ ⟩ prod t u ≡ prod t′ u′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
prod-cong′ {F} {G} {t} {t′} {u} {u′} {Γ} {l} {l′}
           [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′]
           [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext)) with
             B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [prod] = prod′ [F] [t] [Gt] [u] [ΣFG]

      ⊢Γ = wf ⊢F
      [wkF] = [F]₁ id ⊢Γ
      [wkt] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] [wkF] [t]
      [wkt′] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] [wkF] [t′]
      [wkt≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] [wkF] [t≡t′]
      [wkGt] = [G]₁ id ⊢Γ [wkt]
      [wkGt′] = [G]₁ id ⊢Γ [wkt′]
      [wkGt≡Gt′] = G-ext id ⊢Γ [wkt] [wkt′] [wkt≡t′]


      [Gt′] = irrelevance′ (PE.cong (λ x → x [ t′ ]) (wk-lift-id G)) [wkGt′]
      [Gt≡Gt′] = irrelevanceEq″ (PE.cong (λ x → x [ t ]) (wk-lift-id G))
                                (PE.cong (λ x → x [ t′ ]) (wk-lift-id G))
                                [wkGt] [Gt]
                                [wkGt≡Gt′]

      [u′]′ = convTerm₁ [Gt] [Gt′] [Gt≡Gt′] [u′]

      [prod′] = prod′ [F] [t′] [Gt′] [u′]′ [ΣFG]

      [fst] = fst′ [F] [ΣFG] [prod]
      [fst′] = fst′ [F] [ΣFG] [prod′]

      [fst]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                                [F] [wkF]
                                [fst]
      [fst′]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                                 [F] [wkF]
                                 [fst′]

      [fst≡fst′] = {!!}
      [snd≡snd′] = {!!}
  in Σₜ₌ (prod t u)
         (prod t′ u′)
         (idRedTerm:*: (escapeTerm (B-intr BΣ [ΣFG]) [prod]))
         (idRedTerm:*: (escapeTerm (B-intr BΣ [ΣFG]) [prod′]))
         prodₙ prodₙ
         (≅-prod-cong ⊢F ⊢G
                      (escapeTermEq [F] [t≡t′])
                      (escapeTermEq [Gt] [u≡u′]))
         [prod] [prod′]
         [fst]′ [fst′]′
         [fst≡fst′]
         [snd≡snd′]
prod-cong′ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] (emb 0<1 x) =
  prod-cong′ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] x

prod-cong″ : ∀ {F G t t′ u u′ Γ l l′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
             ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ F / [F])
             ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ F / [F])
             ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
             ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ] / [Gt])
             ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Gt])
             ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ F ▹ G)
             → Γ ⊩⟨ l′ ⟩ prod t u ≡ prod t′ u′ ∷ Σ F ▹ G / [ΣFG]
prod-cong″ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] [ΣFG] =
  let [prod≡] = prod-cong′ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] (B-elim BΣ [ΣFG])
  in  irrelevanceEqTerm (B-intr BΣ (B-elim BΣ [ΣFG])) [ΣFG] [prod≡]

prod-congᵛ : ∀ {F G t t′ u u′ Γ l}
             ([Γ] : ⊩ᵛ Γ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
             ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
             ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ F / [Γ] / [F])
             ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ F / [Γ] / [F])
             ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t])
             ([u′] : Γ ⊩ᵛ⟨ l ⟩ u′ ∷ G [ t′ ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t′])
             ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Γ] / substS {F} {G} [Γ] [F] [G] [t])
             → Γ ⊩ᵛ⟨ l ⟩ prod t u ≡ prod t′ u′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G]
prod-congᵛ {F} {G} {t} {t′} {u} {u′} {Γ} [Γ] [F] [G] [t] [t′] [t≡t′] [u] [u′] [u≡u′] {Δ} {σ} ⊢Δ [σ] =
  let ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σt′ = proj₁ ([t′] ⊢Δ [σ])
      σt≡σt′ = [t≡t′] ⊢Δ [σ]

      [Gt] = substS {F} {G} [Γ] [F] [G] [t]
      ⊩σGt₁ = proj₁ ([Gt] ⊢Δ [σ])
      ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

      ⊩σu = irrelevanceTerm′ (singleSubstLift G t)
                             ⊩σGt₁ ⊩σGt
                             (proj₁ ([u] ⊢Δ [σ]))

      [Gt≡Gt′] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = t} {t′ = t′} [Γ]
                          [F] [F] (reflᵛ {A = F} [Γ] [F])
                          [G] [G] (reflᵛ {A = G} {Γ = Γ ∙ F} ([Γ] ∙ [F]) [G])
                          [t] [t′] [t≡t′]
      σGt≡σGt′ = [Gt≡Gt′] ⊢Δ [σ]

      ⊩σGt′ = proj₁ (substS {F} {G} [Γ] [F] [G] [t′] ⊢Δ [σ])
      ⊩σu′₂ = proj₁ ([u′] ⊢Δ [σ])
      ⊩σu′₁ = convTerm₂ ⊩σGt₁ ⊩σGt′ σGt≡σGt′ ⊩σu′₂
      ⊩σu′ = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu′₁

      σu≡σu′ = irrelevanceEqTerm′ (singleSubstLift G t)
                                  ⊩σGt₁ ⊩σGt
                                  ([u≡u′] ⊢Δ [σ])

      ⊩σΣFG = proj₁ (Σᵛ {F} {G} [Γ] [F] [G] ⊢Δ [σ])
  in prod-cong″ ⊩σF ⊩σt ⊩σt′ σt≡σt′ ⊩σGt ⊩σu ⊩σu′ σu≡σu′ ⊩σΣFG

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

      ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape ⊩σF
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σGt′ : Δ ⊩⟨ l ⟩ subst σ (G [ t ])
      ⊩σGt′ = proj₁ ([Gt] ⊢Δ [σ])
      ⊩σGt : Δ ⊩⟨ l ⟩ subst (liftSubst σ) G [ subst σ t ]
      ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt′
      ⊩σu′ = proj₁ ([u] ⊢Δ [σ])
      ⊩σu : Δ ⊩⟨ l ⟩ subst σ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σGt
      ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt ⊩σu′
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])

  in  prod″ ⊩σF ⊩σt ⊩σGt ⊩σu ⊩σΣFG ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let ⊩σ′F = proj₁ ([F] ⊢Δ [σ′])
            σF≡σ′F = proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′t = proj₁ ([t] ⊢Δ [σ′])
            ⊩σ′t = convTerm₂ ⊩σF ⊩σ′F σF≡σ′F ⊩σ′t
            σt≡σ′t = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′Gt′ = proj₁ ([Gt] ⊢Δ [σ′])
            ⊩σ′Gt = irrelevance′ (singleSubstLift G t) ⊩σ′Gt′

            σGt≡σ′Gt = proj₂ ([Gt] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′u″ = proj₁ ([u] ⊢Δ [σ′])
            ⊩σ′u′ = convTerm₂ ⊩σGt′ ⊩σ′Gt′ σGt≡σ′Gt ⊩σ′u″
            ⊩σ′u = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt ⊩σ′u′

            σu≡σ′u : Δ ⊩⟨ l ⟩ subst σ u ≡ subst σ′ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σGt
            σu≡σ′u = irrelevanceEqTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])
        in  prod-cong″ ⊩σF ⊩σt ⊩σ′t σt≡σ′t ⊩σGt ⊩σu ⊩σ′u σu≡σ′u ⊩σΣFG)
