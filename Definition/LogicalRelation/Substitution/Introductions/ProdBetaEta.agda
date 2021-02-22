{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
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

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

Σ-β₁ᵛ : ∀ {F G t u l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F = F} {G} [Γ] [F] [G] [t])
      → Γ ⊩ᵛ⟨ l ⟩ fst (prod t u) ≡ t ∷ F / [Γ] / [F]
Σ-β₁ᵛ {Γ = Γ} {F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] =
  let [Gt] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
      fst⇒t : Γ ⊩ᵛ fst (prod t u) ⇒ t ∷ F / [Γ]
      fst⇒t = (λ {_} {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ ([F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
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
  in  proj₂ (redSubstTermᵛ {A = F} {fst (prod t u)} {t} [Γ] fst⇒t [F] [t])

Σ-β₂ᵛ : ∀ {F G t u l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS {F = F} {G} [Γ] [F] [G] [t])
      → Γ ⊩ᵛ⟨ l ⟩ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ] / [Γ]
          / substS {F = F} {G} [Γ] [F] [G]
                   (fstᵛ {F = F} {G} {prod t u} [Γ] [F] [G]
                         (prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]))
Σ-β₂ᵛ {Γ = Γ} {F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] =
  let [Gt] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
      [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
      [fst] = fstᵛ {F = F} {G} {prod t u} [Γ] [F] [G] [prod]
      [Gfst] = substS {F = F} {G} {fst (prod t u)} [Γ] [F] [G] [fst]
      [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
      [Gfst≡Gt] = substSEq {F = F} {F} {G} {G} {fst (prod t u)} {t}
                           [Γ] [F] [F] (reflᵛ {A = F} [Γ] [F])
                               [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                               [fst] [t] [fst≡t]

      [u]Gfst = conv₂ᵛ {t = u} {G [ fst (prod t u) ]} {G [ t ]}
                       [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]

      snd⇒t : Γ ⊩ᵛ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ] / [Γ]
      snd⇒t = (λ {_} {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ ([F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
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
  in  proj₂ (redSubstTermᵛ {A = G [ fst (prod t u) ]} {snd (prod t u)} {u} [Γ] snd⇒t [Gfst] [u]Gfst)

Σ-η′ : ∀ {F G p r l l′}
         ([F] : Γ ⊩⟨ l′ ⟩ F)
         ([Gfstp] : Γ ⊩⟨ l′ ⟩ G [ fst p ])
         ([ΣFG]₁ : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G )
         ([p] : Γ ⊩⟨ l ⟩ p ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁)
         ([r] : Γ ⊩⟨ l ⟩ r ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁)
         ([fst≡] : Γ ⊩⟨ l′ ⟩ fst p ≡ fst r ∷ F / [F])
         ([snd≡] : Γ ⊩⟨ l′ ⟩ snd p ≡ snd r ∷ G [ fst p ] / [Gfstp])
       → Γ ⊩⟨ l ⟩ p ≡ r ∷ Σ F ▹ G / B-intr BΣ [ΣFG]₁
Σ-η′ {Γ = Γ} {F} {G} {p} {r} {l} {l′}
     [F] [Gfstp]
     [ΣFG]₁@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext))
     [p]@(Σₜ p′ dₚ p′Prod p′≅p′ wk[fstp′] wk[sndp′])
     [r]@(Σₜ r′ dᵣ r′Prod r′≅r′ wk[fstr′] wk[sndr′])
     [fst≡]
     [snd≡]
       with B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [ΣFG] = B-intr BΣ [ΣFG]₁
      ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      wk[Gfstp′] = [G]₁ id ⊢Γ wk[fstp′]

      fstp⇒* : Γ ⊢ fst p ⇒* fst p′ ∷ U.wk id F
      fstp⇒* = PE.subst (λ x → Γ ⊢ _ ⇒* _ ∷ x)
                        (PE.sym (wk-id F))
                        (fst-subst* ⊢F ⊢G (redₜ dₚ))
      fstr⇒* = PE.subst (λ x → Γ ⊢ _ ⇒* _ ∷ x)
                        (PE.sym (wk-id F))
                        (fst-subst* ⊢F ⊢G (redₜ dᵣ))

      --wk[fstp≡] : Γ ⊩⟨ l ⟩ fst p ≡ fst p′ ∷ U.wk id F / wk[F]
      wk[fstp] , wk[fstp≡] = redSubst*Term fstp⇒* wk[F] wk[fstp′]
      wk[fstr] , wk[fstr≡] = redSubst*Term fstr⇒* wk[F] wk[fstr′]

      wk[fst≡] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                    [F] wk[F]
                                    [fst≡]
      wk[fst′≡] : Γ ⊩⟨ l ⟩ fst p′ ≡ fst r′ ∷ U.wk id F / wk[F]
      wk[fst′≡] = transEqTerm wk[F]
                             (symEqTerm wk[F] wk[fstp≡])
                             (transEqTerm wk[F] wk[fst≡] wk[fstr≡])

      [p′] : Γ ⊩⟨ l ⟩ p′ ∷ Σ F ▹ G / [ΣFG]
      [p′] = Σₜ p′ (idRedTerm:*: (⊢u-redₜ dₚ)) p′Prod p′≅p′ wk[fstp′] wk[sndp′]
      [r′] = Σₜ r′ (idRedTerm:*: (⊢u-redₜ dᵣ)) r′Prod r′≅r′ wk[fstr′] wk[sndr′]

      sndp⇒*₁ : Γ ⊢ snd p ⇒* snd p′ ∷ G [ fst p ]
      sndp⇒*₁ = snd-subst* [F] [ΣFG] [p′] (redₜ dₚ)
      sndr⇒*₁ = snd-subst* [F] [ΣFG] [r′] (redₜ dᵣ)

      wk[Gfstp] = [G]₁ id ⊢Γ wk[fstp]
      wk[Gfstr] = [G]₁ id ⊢Γ wk[fstr]
      [Gfstr] = irrelevance′ (PE.cong (λ x → x [ fst r ]) (wk-lift-id G)) wk[Gfstr]
      wk[Gfstr′] = [G]₁ id ⊢Γ wk[fstr′]

      [Gfstp≡wkGfstp′] : Γ ⊩⟨ l′ ⟩ G [ fst p ] ≡ U.wk (lift id) G [ fst p′ ] / [Gfstp]
      [Gfstp≡wkGfstp′] = irrelevanceEq′ (PE.cong (λ x → x [ fst p ]) (wk-lift-id G))
                                        ([G]₁ id ⊢Γ wk[fstp]) [Gfstp]
                                        (G-ext id ⊢Γ wk[fstp] wk[fstp′] wk[fstp≡])
      [Gfstr≡Gfstp] : Γ ⊩⟨ _ ⟩ G [ fst r ] ≡ G [ fst p ] / [Gfstr]
      [Gfstr≡Gfstp] = irrelevanceEq″ (PE.cong (λ x → x [ fst r ]) (wk-lift-id G))
                                     (PE.cong (λ x → x [ fst p ]) (wk-lift-id G))
                                     wk[Gfstr] [Gfstr]
                                     (symEq wk[Gfstp] wk[Gfstr]
                                            (G-ext id ⊢Γ wk[fstp] wk[fstr] wk[fst≡]))
      [Gfstr≡wkGfstp′] : Γ ⊩⟨ l ⟩ G [ fst r ] ≡ U.wk (lift id) G [ fst p′ ] / [Gfstr]
      [Gfstr≡wkGfstp′] = transEq [Gfstr] [Gfstp] wk[Gfstp′]
                                 [Gfstr≡Gfstp] [Gfstp≡wkGfstp′]
      [wkGfstr′≡wkGfstp′] : Γ ⊩⟨ l ⟩ U.wk (lift id) G [ fst r′ ] ≡ U.wk (lift id) G [ fst p′ ] / wk[Gfstr′]
      [wkGfstr′≡wkGfstp′] = G-ext id ⊢Γ wk[fstr′] wk[fstp′] (symEqTerm wk[F] wk[fst′≡])

      sndp⇒* : Γ ⊢ snd p ⇒* snd p′ ∷ U.wk (lift id) G [ fst p′ ]
      sndp⇒* = conv* sndp⇒*₁ (≅-eq (escapeEq [Gfstp] [Gfstp≡wkGfstp′]))
      sndr⇒* = conv* sndr⇒*₁ (≅-eq (escapeEq [Gfstr] [Gfstr≡wkGfstp′]))

      wk[sndp≡] : Γ ⊩⟨ l ⟩ snd p ≡ snd p′ ∷ U.wk (lift id) G [ fst p′ ] / wk[Gfstp′]
      wk[sndp≡] = proj₂ (redSubst*Term sndp⇒* wk[Gfstp′] wk[sndp′])
      wk[sndr≡] = proj₂ (redSubst*Term sndr⇒* wk[Gfstp′]
                                       (convTerm₁ wk[Gfstr′] wk[Gfstp′]
                                                  [wkGfstr′≡wkGfstp′]
                                                  wk[sndr′]))

      wk[snd≡] : Γ ⊩⟨ l ⟩ snd p ≡ snd r ∷ U.wk (lift id) G [ fst p′ ] / wk[Gfstp′]
      wk[snd≡] = convEqTerm₁ [Gfstp] wk[Gfstp′] [Gfstp≡wkGfstp′] [snd≡]

      wk[snd′≡] : Γ ⊩⟨ l ⟩ snd p′ ≡ snd r′ ∷ U.wk (lift id) G [ fst p′ ] / wk[Gfstp′]
      wk[snd′≡] = transEqTerm wk[Gfstp′]
                              (symEqTerm wk[Gfstp′] wk[sndp≡])
                              (transEqTerm wk[Gfstp′] wk[snd≡] wk[sndr≡])

      p′≅r′ : Γ ⊢ p′ ≅ r′ ∷ Σ F ▹ G
      p′≅r′ = ≅-Σ-η ⊢F ⊢G (⊢u-redₜ dₚ) (⊢u-redₜ dᵣ)
                    p′Prod r′Prod
                    (PE.subst (λ x → Γ ⊢ _ ≅ _ ∷ x)
                              (wk-id F)
                              (escapeTermEq wk[F] wk[fst′≡]))
                    (PE.subst (λ x → Γ ⊢ _ ≅ _ ∷ x [ fst p′ ])
                              (wk-lift-id G)
                              (escapeTermEq wk[Gfstp′] wk[snd′≡]))
  in  Σₜ₌ p′ r′ dₚ dᵣ p′Prod r′Prod
          p′≅r′ [p] [r]
          wk[fstp′]
          wk[fstr′]
          wk[fst′≡]
          wk[snd′≡]
Σ-η′ [F] [Gfst] (emb 0<1 x) = Σ-η′ [F] [Gfst] x

Σ-η″ : ∀ {F G p r l}
        ([F] : Γ ⊩⟨ l ⟩ F)
        ([Gfst] : Γ ⊩⟨ l ⟩ G [ fst p ])
        ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
        ([p] : Γ ⊩⟨ l ⟩ p ∷ Σ F ▹ G / [ΣFG])
        ([r] : Γ ⊩⟨ l ⟩ r ∷ Σ F ▹ G / [ΣFG])
        ([fst≡] : Γ ⊩⟨ l ⟩ fst p ≡ fst r ∷ F / [F])
        ([snd≡] : Γ ⊩⟨ l ⟩ snd p ≡ snd r ∷ G [ fst p ] / [Gfst])
      → Γ ⊩⟨ l ⟩ p ≡ r ∷ Σ F ▹ G / [ΣFG]
Σ-η″ {Γ = Γ} {F} {G} {t} {l} [F] [Gfst] [ΣFG] [p] [r] [fst≡] [snd≡] =
  let [ΣFG]′ = B-intr BΣ (B-elim BΣ [ΣFG])
      [p]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [p]
      [r]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [r]
      [p≡]′ = Σ-η′ [F] [Gfst] (B-elim BΣ [ΣFG]) [p]′ [r]′ [fst≡] [snd≡]
  in  irrelevanceEqTerm [ΣFG]′ [ΣFG] [p≡]′

Σ-ηᵛ : ∀ {F G p r l}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       → let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] in
         ([p] : Γ ⊩ᵛ⟨ l ⟩ p ∷ Σ F ▹ G / [Γ] / [ΣFG])
         ([r] : Γ ⊩ᵛ⟨ l ⟩ r ∷ Σ F ▹ G / [Γ] / [ΣFG])
         ([fst≡] : Γ ⊩ᵛ⟨ l ⟩ fst p ≡ fst r ∷ F / [Γ] / [F])
       → let [Gfst] = substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {p} [Γ] [F] [G] [p]) in
         ([snd≡] : Γ ⊩ᵛ⟨ l ⟩ snd p ≡ snd r ∷ G [ fst p ] / [Γ] / [Gfst])
       → Γ ⊩ᵛ⟨ l ⟩ p ≡ r ∷ Σ F ▹ G / [Γ] / [ΣFG]
Σ-ηᵛ {Γ = Γ} {F} {G} {p} {r} {l} [Γ] [F] [G] [p] [r] [fst≡] [snd≡] {Δ} {σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      [Gfst] = substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {p} [Γ] [F] [G] [p])
      ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊩σGfst₁ = proj₁ ([Gfst] ⊢Δ [σ])
      ⊩σGfst = irrelevance′ (singleSubstLift G (fst p)) ⊩σGfst₁
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σp = proj₁ ([p] ⊢Δ [σ])
      ⊩σr = proj₁ ([r] ⊢Δ [σ])
      σfst≡ = [fst≡] ⊢Δ [σ]
      σsnd≡₁ = [snd≡] ⊢Δ [σ]
      σsnd≡ = irrelevanceEqTerm′ (singleSubstLift G (fst p)) ⊩σGfst₁ ⊩σGfst σsnd≡₁
  in  Σ-η″ ⊩σF ⊩σGfst ⊩σΣFG ⊩σp ⊩σr σfst≡ σsnd≡
