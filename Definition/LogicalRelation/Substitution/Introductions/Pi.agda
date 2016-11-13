module Definition.LogicalRelation.Substitution.Introductions.Pi where

open import Definition.Untyped hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product

import Relation.Binary.PropositionalEquality as PE


Πₛ : ∀ {F G Γ l}
     ([Γ] : ⊩ₛ Γ)
     ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
   → Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F]
   → Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ]
Πₛ {F} {G} {Γ} {l} [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ'} [σ'] = [F] {σ = σ'} ⊢Δ [σ']
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ'} [σ'] = soundness (proj₁ ([F]σ {σ'} [σ']))
      [G]σ {σ'} [σ'] = [G] {σ = liftSubst σ'} (⊢Δ ∙ ⊢F [σ'])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ'])
      ⊢G {σ'} [σ'] = soundness (proj₁ ([G]σ {σ'} [σ']))
      ⊢ΠF▹G = Π ⊢F [σ] ▹ ⊢G [σ]
      [G]a : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G)
               (λ [Aσ] →
               {σ' : Nat → Term} →
               (Σ (Δ₁ ⊩ₛ tail σ' ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ' ∷ subst (tail σ') F / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ₛ consSubst (wkSubst (T.toWk ρ) σ) a ≡ σ' ∷ Γ ∙ F /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G ≡
               subst σ' G / [Aσ])
      [G]a a ρ ⊢Δ₁ [a] = ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                          [F] [a]))
      [G]a' : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
            → Δ₁ ⊩⟨ l ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                 / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))
            → Δ₁ ⊩⟨ l ⟩ T.wkLiftₜ ρ (subst (liftSubst σ) G) [ a ]
      [G]a' a ρ ⊢Δ₁ [a] = irrelevance' (PE.sym (G-substWkLemma a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in Π (Π (subst σ F) (subst (liftSubst σ) G)
          (idRed:*: ⊢ΠF▹G) (⊢F [σ]) (⊢G [σ]) (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
          (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
             let [a]' = irrelevanceTerm'
                          (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                          (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
             in  [G]a' a ρ ⊢Δ₁ [a]')
          (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [b] [a≡b] →
             let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                 [a]' = irrelevanceTerm'
                          (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                          (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                 [b]' = irrelevanceTerm'
                          (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                          (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                 [a≡b]' = irrelevanceEqTerm'
                            (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                            (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
             in  irrelevanceEq''
                   (PE.sym (G-substWkLemma a σ G))
                   (PE.sym (G-substWkLemma b σ G))
                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                   ([G]a' a ρ ⊢Δ₁ [a]')
                   (proj₂ ([G]a a ρ ⊢Δ₁ [a]')
                          ([ρσ] , [b]')
                          (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]'))))
  ,  (λ {σ'} [σ'] [σ≡σ'] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → zero ∷ x ∈ (Δ ∙ subst σ F))
                                 (wk-subst F) here)
            [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ]
            [wk1σ'] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ']
            [wk1σ≡wk1σ'] = wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ']
            [F][wk1σ] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
            [F][wk1σ'] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ'])
        in  Π¹[ _ , _ , id (Π ⊢F [σ'] ▹ ⊢G [σ'])
            , Π-cong (⊢F [σ])
                     (soundnessEq (proj₁ ([F] ⊢Δ [σ]))
                                  (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']))
                     (soundnessEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                       ([wk1σ'] , neuTerm [F][wk1σ'] (var zero) (conv var0
                         (soundnessEq [F][wk1σ]
                                      (proj₂ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
                                             [wk1σ'] [wk1σ≡wk1σ']))))
                       ([wk1σ≡wk1σ'] , neuEqTerm [F][wk1σ]
                         (var zero) (var zero) (var0 , var0 , refl var0))))
            , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']))
            , (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
                 let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                     [ρσ'] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ']
                     [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                     [a]'' = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                       (proj₁ ([F] ⊢Δ₁ [ρσ']))
                                       (proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ']
                                              (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']))
                                       [a]'
                     [ρσa≡ρσ'a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                               (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                               (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ'])
                                               [F] [a]'
                 in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                                     (PE.sym (G-substWkLemma a σ' G))
                                     (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                                     ([G]a' a ρ ⊢Δ₁ [a]')
                                     (proj₂ ([G]a a ρ ⊢Δ₁ [a]')
                                            (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ'] , [a]'')
                                            [ρσa≡ρσ'a]))
            ])

Π-congₛ : ∀ {F G H E Γ l}
          ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([H] : Γ ⊩ₛ⟨ l ⟩ H / [Γ])
          ([E] : Γ ∙ H ⊩ₛ⟨ l ⟩ E / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ₛ⟨ l ⟩ F ≡ H / [Γ] / [F])
          ([G≡E] : Γ ∙ F ⊩ₛ⟨ l ⟩ G ≡ E / [Γ] ∙ [F] / [G])
        → Γ ⊩ₛ⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / [Γ] / Πₛ {F} {G} [Γ] [F] [G]
Π-congₛ {F} {G} {H} {E} [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = Πₛ {F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Π F' G' D' ⊢F' ⊢G' [F]' [G]' G-ext' = extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = soundness [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = soundness (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = soundness (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = soundnessEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = soundnessEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  Π¹[ subst σ H
        , subst (liftSubst σ) E
        , id (Π ⊢σH ▹ ⊢σE)
        , Π-cong ⊢σF ⊢σF≡σH ⊢σG≡σE
        , (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                     in  irrelevanceEq'' (PE.sym (wk-subst F))
                                         (PE.sym (wk-subst H))
                                         (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                         ([F]' ρ ⊢Δ₁)
                                         ([F≡H] ⊢Δ₁ [ρσ]))
        , (λ {Δ} {a} ρ ⊢Δ₁ [a] →
             let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                 [a]' = irrelevanceTerm' (wk-subst F)
                                         ([F]' ρ ⊢Δ₁)
                                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                 [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'
             in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                                 (PE.sym (G-substWkLemma a σ E))
                                 (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                 ([G]' ρ ⊢Δ₁ [a])
                                 ([G≡E] ⊢Δ₁ [aρσ])) ]

Πₜₛ : ∀ {F G Γ} ([Γ] : ⊩ₛ Γ)
      ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
      ([U] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
    → Γ ⊩ₛ⟨ ¹ ⟩t F ∷ U / [Γ] / Uₛ [Γ]
    → Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F] / (λ {Δ} {σ} → [U] {Δ} {σ})
    → Γ ⊩ₛ⟨ ¹ ⟩t Π F ▹ G ∷ U / [Γ] / Uₛ [Γ]
Πₜₛ {F} {G} {Γ} [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      ⊢Fₜ = soundnessTerm (U (U ⁰ 0<1 ⊢Δ)) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢Gₜ = soundnessTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                          (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      [F]₀ = univₛ {F} [Γ] (Uₛ [Γ]) [Fₜ]
      [Gₜ]' = S.irrelevanceTerm {A = U} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [U] {Δ} {σ})
                                (λ {Δ} {σ} → Uₛ (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                                [Gₜ]
      [G]₀ = univₛ {G} (_∙_ {A = F} [Γ] [F]₀)
                   (λ {Δ} {σ} → Uₛ (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                   (λ {Δ} {σ} → [Gₜ]' {Δ} {σ})
      [ΠFG] = (Πₛ {F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ]
  in  (Π ⊢Fₜ ▹ ⊢Gₜ , proj₁ [ΠFG])
  ,   (λ [σ'] [σ≡σ'] →
         let [liftσ'] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ']
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ'] = wk1SubstS [Γ] ⊢Δ ⊢F [σ']
             [liftσ']' = [wk1σ']
                       , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ'])) (var zero)
                           (conv (var (⊢Δ ∙ ⊢F)
                                      (PE.subst (λ x → zero ∷ x ∈ (Δ ∙ subst σ F))
                                                (wk-subst F) here))
                                 (soundnessEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                              (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ']
                                                     (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ']))))
             ⊢F' = soundness (proj₁ ([F] ⊢Δ [σ']))
             ⊢Fₜ' = soundnessTerm (U (U ⁰ 0<1 ⊢Δ)) (proj₁ ([Fₜ] ⊢Δ [σ']))
             ⊢Gₜ' = soundnessTerm (proj₁ ([U] (⊢Δ ∙ ⊢F') [liftσ']))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F') [liftσ']))
             ⊢F≡F' = soundnessTermEq (U (U ⁰ 0<1 ⊢Δ))
                                     (proj₂ ([Fₜ] ⊢Δ [σ]) [σ'] [σ≡σ'])
             ⊢G≡G' = soundnessTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ']'
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ']))
             [ΠFG]' = (Πₛ {F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ']
         in  U[ Π ⊢Fₜ ▹ ⊢Gₜ , Π ⊢Fₜ' ▹ ⊢Gₜ' , Π-cong ⊢F ⊢F≡F' ⊢G≡G'
             ,  proj₁ [ΠFG] , proj₁ [ΠFG]' , proj₂ [ΠFG] [σ'] [σ≡σ'] ])

Π-congₜₛ : ∀ {F G H E Γ}
           ([Γ] : ⊩ₛ Γ)
           ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
           ([H] : Γ ⊩ₛ⟨ ¹ ⟩ H / [Γ])
           ([UF] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
           ([UH] : Γ ∙ H ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ₛ⟨ ¹ ⟩t F ∷ U / [Γ] / Uₛ [Γ])
           ([G]ₜ : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F]
                                / (λ {Δ} {σ} → [UF] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ₛ⟨ ¹ ⟩t H ∷ U / [Γ] / Uₛ [Γ])
           ([E]ₜ : Γ ∙ H ⊩ₛ⟨ ¹ ⟩t E ∷ U / [Γ] ∙ [H]
                                / (λ {Δ} {σ} → [UH] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ₛ⟨ ¹ ⟩t' F ≡ H ∷ U / [Γ] / Uₛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t' G ≡ E ∷ U / [Γ] ∙ [F]
                                  / (λ {Δ} {σ} → [UF] {Δ} {σ}))
         → Γ ⊩ₛ⟨ ¹ ⟩t' Π F ▹ G ≡ Π H ▹ E ∷ U / [Γ] / Uₛ [Γ]
Π-congₜₛ {F} {G} {H} {E}
         [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ ⊢Δ [σ] =
  let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      ⊢H = soundness (proj₁ ([H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univₛ {F} [Γ] (Uₛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univₛ {G} {l' = ⁰} (_∙_ {A = F} [Γ] [F])
                    (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F])
                           (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univₛ {H} [Γ] (Uₛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univₛ {E} {l' = ⁰} (_∙_ {A = H} [Γ] [H])
                                  (λ {Δ} {σ} → [UH] {Δ} {σ}) [E]ₜ)
      [F≡H]ᵤ = univEqₛ {F} {H} [Γ] (Uₛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F])
                               (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqₛ {G} {E} (_∙_ {A = F} [Γ] [F])
                          (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ᵤ₁ [G≡E]ₜ)
  in  U[ Π soundnessTerm {l = ¹} (U (U ⁰ 0<1 ⊢Δ)) (proj₁ ([F]ₜ ⊢Δ [σ]))
         ▹ soundnessTerm (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                         (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
       , Π soundnessTerm {l = ¹} (U (U ⁰ 0<1 ⊢Δ)) (proj₁ ([H]ₜ ⊢Δ [σ]))
         ▹ soundnessTerm (proj₁ ([UH] (⊢Δ ∙ ⊢H) [liftHσ]))
                         (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ]))
       , Π-cong ⊢F (soundnessTermEq (U (U ⁰ 0<1 ⊢Δ)) ([F≡H]ₜ ⊢Δ [σ]))
                   (soundnessTermEq (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                                    ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
       , proj₁ (Πₛ {F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ])
       , proj₁ (Πₛ {H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ])
       , Π-congₛ {F} {G} {H} {E} [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ] ]

▹▹ₛ : ∀ {F G Γ l}
      ([Γ] : ⊩ₛ Γ)
      ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
    → Γ ⊩ₛ⟨ l ⟩ G / [Γ]
    → Γ ⊩ₛ⟨ l ⟩ F ▹▹ G / [Γ]
▹▹ₛ {F} {G} [Γ] [F] [G] =
  Πₛ {F} {wk1 G} [Γ] [F] (wk1ₛ {G} {F} [Γ] [F] [G])

▹▹-congₛ : ∀ {F F' G G' Γ l}
           ([Γ] : ⊩ₛ Γ)
           ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
           ([F'] : Γ ⊩ₛ⟨ l ⟩ F' / [Γ])
           ([F≡F'] : Γ ⊩ₛ⟨ l ⟩ F ≡ F' / [Γ] / [F])
           ([G] : Γ ⊩ₛ⟨ l ⟩ G / [Γ])
           ([G'] : Γ ⊩ₛ⟨ l ⟩ G' / [Γ])
           ([G≡G'] : Γ ⊩ₛ⟨ l ⟩ G ≡ G' / [Γ] / [G])
         → Γ ⊩ₛ⟨ l ⟩ F ▹▹ G ≡ F' ▹▹ G' / [Γ] / ▹▹ₛ {F} {G} [Γ] [F] [G]
▹▹-congₛ {F} {F'} {G} {G'} [Γ] [F] [F'] [F≡F'] [G] [G'] [G≡G'] =
  Π-congₛ {F} {wk1 G} {F'} {wk1 G'} [Γ]
          [F] (wk1ₛ {G} {F} [Γ] [F] [G])
          [F'] (wk1ₛ {G'} {F'} [Γ] [F'] [G'])
          [F≡F'] (wk1Eqₛ {G} {G'} {F} [Γ] [F] [G] [G≡G'])
