{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Snd {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Fst

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

snd-subst*′ : ∀ {l l′ F G t t′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ ⟩ Σ F ▹ G)
             ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
             → Γ ⊢ t ⇒* t′ ∷ Σ F ▹ G
             → Γ ⊢ snd t ⇒* snd t′ ∷ G [ fst t ]
snd-subst*′ [F] (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext)) _ (id x) with
              B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl = id (sndⱼ ⊢F ⊢G x)
snd-subst*′ {Γ = Γ} {F = F} {G = G} {t = t} {t′ = t″} [F]
            [ΣFG]₀@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G] G-ext))
            [t″]
            t⇒*t″@(_⇨_ {t′ = t′} t⇒t′ t′⇒*t″) with
              B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let [ΣFG] = B-intr BΣ [ΣFG]₀
      [t] , _ = redSubst*Term t⇒*t″ [ΣFG] [t″]
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
      [fstt′≡fstt] = symEqTerm [F] (fst-cong″ [F] [ΣFG] [t≡t′])
      [Gfstt′≡Gfstt] : Γ ⊩⟨ _ ⟩ G [ fst t′ ] ≡ G [ fst t ] / [Gfstt′]
      [Gfstt′≡Gfstt] = substSΠ₂ BΣ [ΣFG] (reflEq [ΣFG]) [F] [F] [fstt′] [fstt] [fstt′≡fstt] [Gfstt′] [Gfstt]
  in  snd-subst ⊢F ⊢G t⇒t′ ⇨ conv* (snd-subst*′ [F] [ΣFG]₀ [t″] t′⇒*t″)
                                               (≅-eq (escapeEq [Gfstt′] [Gfstt′≡Gfstt]))
snd-subst*′ [F] (emb 0<1 x) = snd-subst*′ [F] x

-- NOTE this has a horrible interface (and implementation)
snd-subst* : ∀ {l l′ F G t t′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ F ▹ G)
             ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ Σ F ▹ G / [ΣFG])
             → Γ ⊢ t ⇒* t′ ∷ Σ F ▹ G
             → Γ ⊢ snd t ⇒* snd t′ ∷ G [ fst t ]
snd-subst* [F] [ΣFG] [t′] t⇒*t′ =
  let [t′]′ = irrelevanceTerm [ΣFG] (B-intr BΣ (B-elim BΣ [ΣFG])) [t′]
  in  snd-subst*′ [F] (B-elim BΣ [ΣFG]) [t′]′ t⇒*t′

snd′ : ∀ {F G t l l′}
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
       → Γ ⊩⟨ l′ ⟩ snd t ∷ G [ fst t ] / [Gfst]
snd′ {Γ = Γ} {F = F} {G = G} {t = t} {l = l} {l′ = l′}
     [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
     [t]@(Σₜ p d pProd p≅p [fstp] [sndp]) [Gfst] with
       B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let ⊢Γ = wf ⊢F
      [p] = Σₜ p (idRedTerm:*: (⊢u-redₜ d)) pProd p≅p [fstp] [sndp]

      [fstt] , [fstt≡fstp] = redSubst*Term (PE.subst (λ x → Γ ⊢ fst t ⇒* fst p ∷ x)
                                                     (PE.sym (wk-id F))
                                                     (fst-subst* ⊢F ⊢G (redₜ d)))
                                           ([F'] id ⊢Γ) [fstp]

      [Gfstt] = [G'] id ⊢Γ [fstt]
      [Gfstp] = [G'] id ⊢Γ [fstp]
      [Gfstt≡Gfstp] = G-ext id ⊢Γ [fstt] [fstp] [fstt≡fstp]

      [sndp] = convTerm₂ [Gfstt] [Gfstp] [Gfstt≡Gfstp] [sndp]

      [sndp] : Γ ⊩⟨ l′ ⟩ snd p ∷ G [ fst t ] / [Gfst]
      [sndp] = irrelevanceTerm′ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                                [Gfstt] [Gfst] [sndp]
  in  proj₁ (redSubst*Term (snd-subst* (PE.subst (λ x → Γ ⊩⟨ l ⟩ x) (wk-id F) ([F'] id ⊢Γ))
                                       (B-intr BΣ [ΣFG])
                                       [p]
                                       (redₜ d))
                           [Gfst]
                           [sndp])
snd′ (emb 0<1 x) = snd′ x

snd″ : ∀ {F G t l l′}
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
       → Γ ⊩⟨ l′ ⟩ snd t ∷ G [ fst t ] / [Gfst]
snd″ {Γ = Γ} {t = t} {l = l} [ΣFG] [t] [Gfst] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
  in  snd′ (Σ-elim [ΣFG]) [t]′ [Gfst]

snd-cong′ : ∀ {F G t t′ l l′}
            ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
            ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
            → Γ ⊩⟨ l′ ⟩ snd t ≡ snd t′ ∷ G [ fst t ] / [Gfst]
snd-cong′ {Γ = Γ} {F} {G} {t} {t′} {l} {l′}
          [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F] [G] G-ext))
          [t]@(Σₜ p d pProd p≅p [fstp] [sndp])
          [t′]@(Σₜ p′ d′ pProd′ p′≅p′ [fstp′] [sndp′])
          [t≡t′]@(Σₜ₌ p₁ p′₁ d₁ d′₁ pProd₁ pProd′₁ p≅p′ [t]₁ [t′]₁ [fstp]₁ [fstp′]₁ [fst≡] [snd≡])
          [Gfst] with
            B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
          | whrDet*Term (redₜ d , productWhnf pProd) (redₜ d₁ , productWhnf pProd₁)
          | whrDet*Term (redₜ d′ , productWhnf pProd′) (redₜ d′₁ , productWhnf pProd′₁)
... | PE.refl , PE.refl | PE.refl | PE.refl =
  let ⊢Γ = wf ⊢F
      [p] : Γ ⊩⟨ l ⟩ p ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
      [p] = Σₜ p (idRedTerm:*: (⊢u-redₜ d)) pProd p≅p [fstp] [sndp]
      [p′] : Γ ⊩⟨ l ⟩ p′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG]
      [p′] = Σₜ p′ (idRedTerm:*: (⊢u-redₜ d′)) pProd′ p′≅p′ [fstp′] [sndp′]
      [F]′ = irrelevance′ (wk-id F) ([F] id ⊢Γ)

      [fstt] , [fstt≡fstp] = redSubst*Term (PE.subst (λ x → Γ ⊢ fst t ⇒* fst p ∷ x)
                                                     (PE.sym (wk-id F))
                                                     (fst-subst* ⊢F ⊢G (redₜ d)))
                                           ([F] id ⊢Γ) [fstp]
      [Gfstt≡Gfstp] = G-ext id ⊢Γ [fstt] [fstp] [fstt≡fstp]

      [sndp]′ : Γ ⊩⟨ l ⟩ snd p ∷ U.wk (lift id) G [ fst t ] / [G] id ⊢Γ [fstt]
      [sndp]′ = convTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp]) [Gfstt≡Gfstp] [sndp]
      sndt⇒*sndp = snd-subst* [F]′ (B-intr BΣ [ΣFG]) [p] (redₜ d)
      [sndp]″ = irrelevanceTerm′ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                                 ([G] id ⊢Γ [fstt]) [Gfst]
                                 [sndp]′
      [sndt≡sndp] : Γ ⊩⟨ l′ ⟩ snd t ≡ snd p ∷ G [ fst t ] / [Gfst]
      [sndt≡sndp] = proj₂ (redSubst*Term sndt⇒*sndp [Gfst] [sndp]″)

      [snd≡]′ = convEqTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp]₁) [Gfstt≡Gfstp] [snd≡]
      [sndp≡sndp′] : Γ ⊩⟨ l′ ⟩ snd p ≡ snd p′ ∷ G [ fst t ] / [Gfst]
      [sndp≡sndp′] = irrelevanceEqTerm′ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                                        ([G] id ⊢Γ [fstt]) [Gfst]
                                        [snd≡]′

      [fstt′] , [fstt′≡fstp′] = redSubst*Term (PE.subst (λ x → Γ ⊢ fst t′ ⇒* fst p′ ∷ x)
                                                     (PE.sym (wk-id F))
                                                     (fst-subst* ⊢F ⊢G (redₜ d′)))
                                           ([F] id ⊢Γ) [fstp′]
      [fstt≡fstt′] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                        [F]′ ([F] id ⊢Γ)
                                        (fst-cong′ [F]′ [ΣFG] [t≡t′])
      [fstt≡fstp′] = transEqTerm ([F] id ⊢Γ) [fstt≡fstt′] [fstt′≡fstp′]
      [Gfstt≡Gfstp′] = G-ext id ⊢Γ [fstt] [fstp′] [fstt≡fstp′]
      [sndp′]′ : Γ ⊩⟨ l ⟩ snd p′ ∷ U.wk (lift id) G [ fst t ] / [G] id ⊢Γ [fstt]
      [sndp′]′ = convTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp′]) [Gfstt≡Gfstp′] [sndp′]
      [sndp′]″ = irrelevanceTerm′ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                                  ([G] id ⊢Γ [fstt]) [Gfst]
                                  [sndp′]′
      [Gfstt]′ = irrelevance′ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                              ([G] id ⊢Γ [fstt])
      [Gfstt≡Gfstt′] = irrelevanceEq″ (PE.cong (λ x → x [ fst t ]) (wk-lift-id G))
                                      (PE.cong (λ x → x [ fst t′ ]) (wk-lift-id G))
                                      ([G] id ⊢Γ [fstt]) [Gfstt]′
                                      (G-ext id ⊢Γ [fstt] [fstt′] [fstt≡fstt′])
      sndt′⇒*sndp′ : Γ ⊢ snd t′ ⇒* snd p′ ∷ G [ fst t ]
      sndt′⇒*sndp′ = conv* (snd-subst* [F]′ (B-intr BΣ [ΣFG]) [p′] (redₜ d′))
                           (≅-eq (≅-sym (escapeEq [Gfstt]′ [Gfstt≡Gfstt′])))
      [sndt′≡sndp′] : Γ ⊩⟨ l′ ⟩ snd t′ ≡ snd p′ ∷ G [ fst t ] / [Gfst]
      [sndt′≡sndp′] = proj₂ (redSubst*Term sndt′⇒*sndp′ [Gfst] [sndp′]″)

  in  transEqTerm [Gfst] [sndt≡sndp] (transEqTerm [Gfst] [sndp≡sndp′] (symEqTerm [Gfst] [sndt′≡sndp′]))
snd-cong′ {F} {G} (emb 0<1 x) = snd-cong′ x

snd-cong″ : ∀ {F G t t′ l l′}
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
            ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ F ▹ G / [ΣFG])
            ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σ F ▹ G / [ΣFG])
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [ΣFG])
            ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst t ])
            → Γ ⊩⟨ l′ ⟩ snd t ≡ snd t′ ∷ G [ fst t ] / [Gfst]
snd-cong″ {F} {G} [ΣFG] [t] [t′] [t≡t′] [Gfst] =
  let [t] = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t]
      [t′] = irrelevanceTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t′]
      [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t≡t′]
  in  snd-cong′ (B-elim BΣ [ΣFG]) [t] [t′] [t≡t′] [Gfst]

snd-congᵛ : ∀ {F G t t′ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
          → Γ ⊩ᵛ⟨ l ⟩ snd t ≡ snd t′ ∷ G [ fst t ] / [Γ] / substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t])
snd-congᵛ {Γ = Γ} {F} {G} {t} {t′} {l} [Γ] [F] [G] [t] [t′] [t≡t′] {Δ} {σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]
      [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]

      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σt′ = proj₁ ([t′] ⊢Δ [σ])
      σt≡σt′ = [t≡t′] ⊢Δ [σ]

      ⊩σGfst₁ = proj₁ ([Gfst] ⊢Δ [σ])
      ⊩σGfst = irrelevance′ (singleSubstLift G (fst t)) ⊩σGfst₁

      σsnd≡₁ = snd-cong″ ⊩σΣFG ⊩σt ⊩σt′ σt≡σt′ ⊩σGfst
      σsnd≡ = irrelevanceEqTerm′ (PE.sym (singleSubstLift G (fst t))) ⊩σGfst ⊩σGfst₁ σsnd≡₁
  in  σsnd≡

-- Validity of second projection
sndᵛ : ∀ {F G t l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
       → Γ ⊩ᵛ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t])
sndᵛ {Γ = Γ} {F} {G} {t} {l} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      [Gfst] : Γ ⊩ᵛ⟨ l ⟩ G [ fst t ] / [Γ]
      [Gfst] = substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t])

      σsnd : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ subst σ (snd t) ∷ subst σ (G [ fst t ]) / proj₁ ([Gfst] ⊢Δ [σ])
      σsnd {Δ} {σ} ⊢Δ [σ] =
        let ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
            ⊩σGfstt = proj₁ ([Gfst] ⊢Δ [σ])
            ⊩σGfstt′ = PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (singleSubstLift G (fst t)) ⊩σGfstt
            ⊩σsnd = snd″ ⊩σΣFG ⊩σt ⊩σGfstt′
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
            [σGfstt] = proj₁ ([Gfst] ⊢Δ [σ])
            [σGfstt]′ = PE.subst (λ x → _ ⊩⟨ l ⟩ x)
                                (singleSubstLift G (fst t))
                                [σGfstt]
            [sndt≡sndt′] = snd-cong″ [σΣFG] [σt] [σ′t] [σt≡σ′t] [σGfstt]′
        in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G (fst t)))
                               [σGfstt]′ [σGfstt]
                               [sndt≡sndt′])
