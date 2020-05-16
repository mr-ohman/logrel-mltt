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
                               [G] [G] (reflᵛ {G} {Γ ∙ F} ([Γ] ∙ [F]) [G])
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

Σ-η′ : ∀ {F G t Γ l}
        ([ΣFG]₁ : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G )
        ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁)
        ([prod] : Γ ⊩⟨ l ⟩ prod (fst t) (snd t) ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁)
      → Γ ⊩⟨ l ⟩ t ≡ prod (fst t) (snd t) ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁
Σ-η′ {F} {G} {t} {Γ} {l}
     [ΣFG]₁@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext))
     [t]@(Σₜ p d pProd p≅p wk[fstp] wk[sndp])
     [prod]@(Σₜ _ d′ _ _ wk[fstprod] wk[sndprod])
       with B-PE-injectivity BΣ (whnfRed* (red D) Σₙ) | whnfRed*Term (redₜ d′) prodₙ
... | PE.refl , PE.refl | PE.refl =
      -- some types
  let [ΣFG] = B-intr BΣ [ΣFG]₁
      ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      [F] = irrelevance′ (wk-id F) wk[F]

      -- eta congruence of WHNFs
      [fstp] = irrelevanceTerm′ (wk-id F) wk[F] [F] wk[fstp]
      fstt⇒*fstp : Γ ⊢ fst t ⇒* fst p ∷ F
      fstt⇒*fstp = fst-subst* ⊢F ⊢G (redₜ d)
      [fstt] , [fstt≡fstp] = redSubst*Term fstt⇒*fstp [F] [fstp]
      fstt≅fstp : Γ ⊢ fst t ≅ fst p ∷ F
      fstt≅fstp = escapeTermEq [F] [fstt≡fstp]

      wk[fstt] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [fstt]
      wk[fstt≡fstp] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [fstt≡fstp]
      wk[Gfstt] = [G]₁ id ⊢Γ wk[fstt]
      wkLiftIdFstt = PE.cong (λ x → x [ fst t ]) (wk-lift-id G)
      wkLiftIdFstp = PE.cong (λ x → x [ fst p ]) (wk-lift-id G)
      [Gfstt] = irrelevance′ wkLiftIdFstt wk[Gfstt]
      wk[Gfstp] = [G]₁ id ⊢Γ wk[fstp]
      [Gfstp] = irrelevance′ wkLiftIdFstp wk[Gfstp]
      wk[Gfstt≡Gfstp] = G-ext id ⊢Γ wk[fstt] wk[fstp] wk[fstt≡fstp]
      [Gfstt≡Gfstp] = irrelevanceEq″ wkLiftIdFstt wkLiftIdFstp wk[Gfstt] [Gfstt] wk[Gfstt≡Gfstp]

      [sndp]₁ = irrelevanceTerm′ wkLiftIdFstp wk[Gfstp] [Gfstp] wk[sndp]
      [sndp] : Γ ⊩⟨ l ⟩ snd p ∷ G [ fst t ] / [Gfstt]
      [sndp] = convTerm₂ [Gfstt] [Gfstp] [Gfstt≡Gfstp] [sndp]₁

      sndt⇒*sndp : Γ ⊢ snd t ⇒* snd p ∷ G [ fst t ]
      sndt⇒*sndp = snd-subst* [F] [ΣFG]
                              (Σₜ p (idRedTerm:*: (⊢u-redₜ d)) pProd
                                  p≅p wk[fstp] wk[sndp])
                              (redₜ d)
      [sndt] , [sndt≡sndp] = redSubst*Term sndt⇒*sndp [Gfstt] [sndp]
      sndt≅sndp : Γ ⊢ snd t ≅ snd p ∷ G [ fst t ]
      sndt≅sndp = escapeTermEq [Gfstt] [sndt≡sndp]

      prodt≅prodp : Γ ⊢ prod (fst t) (snd t) ≅ prod (fst p) (snd p) ∷ Σ F ▹ G
      prodt≅prodp = ≅-prod-cong ⊢F ⊢G fstt≅fstp sndt≅sndp

      p≅prodp : Γ ⊢ p ≅ prod (fst p) (snd p) ∷ Σ F ▹ G
      p≅prodp = ≅-Σ-η ⊢F ⊢G (⊢u-redₜ d) pProd
      p≅prodt : Γ ⊢ p ≅ prod (fst t) (snd t) ∷ Σ F ▹ G
      p≅prodt = ≅ₜ-trans p≅prodp (≅ₜ-sym prodt≅prodp)

      -- fst congruence
      fstprod⇒fstt : Γ ⊢ fst (prod (fst t) (snd t)) ⇒ fst t ∷ F
      fstprod⇒fstt = Σ-β₁ ⊢F ⊢G (escapeTerm [F] [fstt]) (escapeTerm [Gfstt] [sndt])
      fstprod⇒*fstp : Γ ⊢ fst (prod (fst t) (snd t)) ⇒* fst p ∷ F
      fstprod⇒*fstp = fstprod⇒fstt ⇨ fstt⇒*fstp

      [fstprod] , [fstprod≡fstp] = redSubst*Term fstprod⇒*fstp [F] [fstp]
      wk[fstprod≡fstp] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [fstprod≡fstp]

      wk[fst≡] : Γ ⊩⟨ l ⟩ fst p ≡ fst (prod (fst t) (snd t)) ∷ U.wk id F / wk[F]
      wk[fst≡] = symEqTerm wk[F] wk[fstprod≡fstp]

      -- snd congruence
      sndprod⇒sndt₁ : Γ ⊢ _ ⇒ _ ∷ _
      sndprod⇒sndt₁ = Σ-β₂ ⊢F ⊢G (escapeTerm [F] [fstt]) (escapeTerm [Gfstt] [sndt])

      wkLiftIdFstProd = PE.cong (λ x → x [ fst (prod (fst t) (snd t)) ]) (wk-lift-id G)
      wk[Gfstprod] = [G]₁ id ⊢Γ wk[fstprod]
      [Gfstprod] = irrelevance′ wkLiftIdFstProd wk[Gfstprod]

      wk[Gfstprod≡Gfstp] = G-ext id ⊢Γ wk[fstprod] wk[fstp] wk[fstprod≡fstp]
      [Gfstprod≡Gfstp] = irrelevanceEq″ wkLiftIdFstProd wkLiftIdFstp
                                        wk[Gfstprod] [Gfstprod]
                                        wk[Gfstprod≡Gfstp]

      sndprod⇒sndt : Γ ⊢ snd (prod (fst t) (snd t)) ⇒ snd t ∷ G [ fst p ]
      sndprod⇒sndt = conv sndprod⇒sndt₁ (≅-eq (escapeEq [Gfstprod] [Gfstprod≡Gfstp]))

      sndprod⇒*sndp : Γ ⊢ snd (prod (fst t) (snd t)) ⇒* snd p ∷ G [ fst p ]
      sndprod⇒*sndp = sndprod⇒sndt ⇨ conv* sndt⇒*sndp (≅-eq (escapeEq [Gfstt] [Gfstt≡Gfstp]))
      [sndprod≡sndp] : Γ ⊩⟨ l ⟩ snd (prod (fst t) (snd t)) ≡ snd p ∷ G [ fst p ] / [Gfstp]
      [sndprod≡sndp] = proj₂ (redSubst*Term sndprod⇒*sndp [Gfstp] [sndp]₁)
      wk[sndprod≡sndp] = irrelevanceEqTerm′ (PE.sym wkLiftIdFstp) [Gfstp] wk[Gfstp] [sndprod≡sndp]

      wk[snd≡] : Γ ⊩⟨ l ⟩ snd p ≡ snd (prod (fst t) (snd t)) ∷ U.wk (lift id) G [ fst p ] / wk[Gfstp]
      wk[snd≡] = symEqTerm wk[Gfstp] wk[sndprod≡sndp]
  in  Σₜ₌ p (prod (fst t) (snd t))
          d (idRedTerm:*: (escapeTerm [ΣFG] [prod]))
          pProd prodₙ
          p≅prodt
          [t] [prod]
          wk[fstp] wk[fstprod]
          wk[fst≡]
          wk[snd≡]
Σ-η′ (emb 0<1 x) = Σ-η′ x

Σ-η″ : ∀ {F G t Γ l}
        ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G )
        ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
        ([prod] : Γ ⊩⟨ l ⟩ prod (fst t) (snd t) ∷ Σ F ▹ G / [ΣFG])
      → Γ ⊩⟨ l ⟩ t ≡ prod (fst t) (snd t) ∷ Σ F ▹ G / [ΣFG]
Σ-η″ {F} {G} {t} {Γ} {l} [ΣFG] [t] [prod] =
  let [ΣFG]′ = B-intr BΣ (B-elim BΣ [ΣFG])
      [t]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [t]
      [prod]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [prod]
      [η] = Σ-η′ (B-elim BΣ [ΣFG]) [t]′ [prod]′
  in  irrelevanceEqTerm [ΣFG]′ [ΣFG] [η]

Σ-ηᵛ : ∀ {F G t Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G])
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ prod (fst t) (snd t) ∷ Σ F ▹ G / [Γ] / Σᵛ {F} {G} [Γ] [F] [G]
Σ-ηᵛ {F} {G} {t} {Γ} {l} [Γ] [F] [G] [t] {Δ} {σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F} {G} [Γ] [F] [G]
      [fst] = fstᵛ {F} {G} {t} [Γ] [F] [G] [t]
      [snd] = sndᵛ {F} {G} {t} [Γ] [F] [G] [t]
      [prod] = prodᵛ {F} {G} {fst t} {snd t} [Γ] [F] [G] [fst] [snd]
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σprod = proj₁ ([prod] ⊢Δ [σ])
  in  Σ-η″ ⊩σΣFG ⊩σt ⊩σprod
