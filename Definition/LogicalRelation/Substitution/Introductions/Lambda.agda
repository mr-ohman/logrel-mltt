open import Definition.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Lambda {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.Pi

open import Tools.Nat
open import Tools.Product

import Tools.PropositionalEquality as PE


lamₛ : ∀ {F G t Γ}
       ([Γ] : ⊩ₛ Γ)
       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t t ∷ G / [Γ] ∙ [F] / [G])
     → Γ ⊩ₛ⟨ ¹ ⟩t lam t ∷ Π F ▹ G / [Γ] / Πₛ {F} {G} [Γ] [F] [G]
lamₛ {F} {G} {t} {Γ} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢F = wellformed (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [ΠFG] = Πₛ {F} {G} [Γ] [F] [G]
      _ , Π F' G' D' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext =
        extractMaybeEmb (Π-elim (proj₁ ([ΠFG] ⊢Δ [σ])))
      lamt : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ ¹ ⟩ subst σ (lam t) ∷ subst σ (Π F ▹ G) / proj₁ ([ΠFG] ⊢Δ [σ])
      lamt {Δ} {σ} ⊢Δ [σ] =
        let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
            [σF] = proj₁ ([F] ⊢Δ [σ])
            ⊢F = wellformed [σF]
            [σG] = proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ])
            ⊢G = wellformed [σG]
            [σt] = proj₁ ([t] (⊢Δ ∙ ⊢F) [liftσ])
            ⊢t = wellformedTerm [σG] [σt]
            _ , Π F' G' D' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext =
              extractMaybeEmb (Π-elim (proj₁ ([ΠFG] ⊢Δ [σ])))
        in  Πₜ (lam (subst (liftSubst σ) t)) (idRedTerm:*: (lam ⊢F ⊢t)) lam
               (≅ₜ-lamrefl ⊢F ⊢t)
               (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [b] [a≡b] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                      [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁)
                                              (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      [b]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁)
                                              (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                      [a≡b]' = irrelevanceEqTerm' (wk-subst F) ([F]' ρ ⊢Δ₁)
                                                  (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
                      ⊢F₁' = wellformed (proj₁ ([F] ⊢Δ₁ [ρσ]))
                      ⊢F₁ = wellformed ([F]' ρ ⊢Δ₁)
                      [G]₁ = proj₁ ([G] (⊢Δ₁ ∙ ⊢F₁')
                                        (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                      [G]₁' = irrelevanceΓ'
                                (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                                (PE.sym (G-lamLemma G)) [G]₁
                      [t]' = irrelevanceTermΓ''
                               (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                               (PE.sym (G-lamLemma G))
                               (PE.sym (G-lamLemma t))
                               [G]₁ [G]₁'
                               (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁')
                                           (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                      ⊢a = wellformedTerm ([F]' ρ ⊢Δ₁) [a]
                      ⊢b = wellformedTerm ([F]' ρ ⊢Δ₁) [b]
                      ⊢t = wellformedTerm [G]₁' [t]'
                      G[a]' = proj₁ ([G] ⊢Δ₁ ([ρσ] , [a]'))
                      G[a] = [G]' ρ ⊢Δ₁ [a]
                      t[a] = irrelevanceTerm''
                               (PE.sym (G-substWkLemma a σ G))
                               (PE.sym (G-substWkLemma a σ t))
                               G[a]' G[a]
                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]')))
                      G[b]' = proj₁ ([G] ⊢Δ₁ ([ρσ] , [b]'))
                      G[b] = [G]' ρ ⊢Δ₁ [b]
                      t[b] = irrelevanceTerm''
                               (PE.sym (G-substWkLemma b σ G))
                               (PE.sym (G-substWkLemma b σ t))
                               G[b]' G[b]
                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [b]')))
                      lamt∘a≡t[a] = proj₂ (redSubstTerm (β-red ⊢F₁ ⊢t ⊢a) G[a] t[a])
                      G[a]≡G[b] = G-ext ρ ⊢Δ₁ [a] [b] [a≡b]
                      t[a]≡t[b] = irrelevanceEqTerm''
                                    (PE.sym (G-substWkLemma a σ t))
                                    (PE.sym (G-substWkLemma b σ t))
                                    (PE.sym (G-substWkLemma a σ G))
                                    G[a]' G[a]
                                    (proj₂ ([t] ⊢Δ₁ ([ρσ] , [a]')) ([ρσ] , [b]')
                                                (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]'))
                      t[b]≡lamt∘b =
                        convEqTerm₂ G[a] G[b] G[a]≡G[b]
                          (symEqTerm G[b] (proj₂ (redSubstTerm (β-red ⊢F₁ ⊢t ⊢b)
                                                               G[b] t[b])))
                  in  transEqTerm G[a] lamt∘a≡t[a]
                             (transEqTerm G[a] t[a]≡t[b] t[b]≡lamt∘b))
               (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                      [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁)
                                              (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      ⊢F₁' = wellformed (proj₁ ([F] ⊢Δ₁ [ρσ]))
                      ⊢F₁ = wellformed ([F]' ρ ⊢Δ₁)
                      [G]₁ = proj₁ ([G] (⊢Δ₁ ∙ ⊢F₁')
                                        (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                      [G]₁' = irrelevanceΓ'
                                (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                                (PE.sym (G-lamLemma G)) [G]₁
                      [t]' = irrelevanceTermΓ''
                               (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                               (PE.sym (G-lamLemma G))
                               (PE.sym (G-lamLemma t))
                               [G]₁ [G]₁'
                               (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁')
                                           (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                      ⊢a = wellformedTerm ([F]' ρ ⊢Δ₁) [a]
                      ⊢t = wellformedTerm [G]₁' [t]'
                      G[a]' = proj₁ ([G] ⊢Δ₁ ([ρσ] , [a]'))
                      G[a] = [G]' ρ ⊢Δ₁ [a]
                      t[a] = irrelevanceTerm'' (PE.sym (G-substWkLemma a σ G))
                                               (PE.sym (G-substWkLemma a σ t))
                                               G[a]' G[a]
                                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]')))
                  in  proj₁ (redSubstTerm (β-red ⊢F₁ ⊢t ⊢a) G[a] t[a]))
  in  lamt ⊢Δ [σ]
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         let [liftσ'] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ']
             _ , Π F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F]'' [G]'' G-ext' =
               extractMaybeEmb (Π-elim (proj₁ ([ΠFG] ⊢Δ [σ'])))
             ⊢F' = wellformed (proj₁ ([F] ⊢Δ [σ']))
             [G]₁ = proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ])
             [G]₁' = proj₁ ([G] (⊢Δ ∙ ⊢F') [liftσ'])
             [σΠFG≡σ'ΠFG] = proj₂ ([ΠFG] ⊢Δ [σ]) [σ'] [σ≡σ']
             ⊢t = wellformedTerm [G]₁ (proj₁ ([t] (⊢Δ ∙ ⊢F) [liftσ]))
             ⊢t' = wellformedTerm [G]₁' (proj₁ ([t] (⊢Δ ∙ ⊢F') [liftσ']))
             neuVar = neuTerm ([F]' (T.step T.id) (⊢Δ ∙ ⊢F))
                              (var 0) (var (⊢Δ ∙ ⊢F) here)
             σlamt∘a≡σ'lamt∘a : ∀ {Δ₁ a} → (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
                 → ([a] : Δ₁ ⊩⟨ ¹ ⟩ a ∷ T.wkₜ ρ (subst σ F) / [F]' ρ ⊢Δ₁)
                 → Δ₁ ⊩⟨ ¹ ⟩ T.wkₜ ρ (subst σ (lam t)) ∘ a
                           ≡ T.wkₜ ρ (subst σ' (lam t)) ∘ a
                           ∷ T.wkLiftₜ ρ (subst (liftSubst σ) G) [ a ]
                           / [G]' ρ ⊢Δ₁ [a]
             σlamt∘a≡σ'lamt∘a {Δ₁} {a} ρ ⊢Δ₁ [a] =
                let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    [ρσ'] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ']
                    [ρσ≡ρσ'] = wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']
                    ⊢F₁' = wellformed (proj₁ ([F] ⊢Δ₁ [ρσ]))
                    ⊢F₁ = wellformed ([F]' ρ ⊢Δ₁)
                    ⊢F₂' = wellformed (proj₁ ([F] ⊢Δ₁ [ρσ']))
                    ⊢F₂ = wellformed ([F]'' ρ ⊢Δ₁)
                    [σF≡σ'F] = proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ'] [ρσ≡ρσ']
                    [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁)
                                            (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                    [a]'' = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                      (proj₁ ([F] ⊢Δ₁ [ρσ']))
                                      [σF≡σ'F] [a]'
                    ⊢a = wellformedTerm ([F]' ρ ⊢Δ₁) [a]
                    ⊢a' = wellformedTerm ([F]'' ρ ⊢Δ₁)
                            (irrelevanceTerm' (PE.sym (wk-subst F))
                                              (proj₁ ([F] ⊢Δ₁ [ρσ']))
                                              ([F]'' ρ ⊢Δ₁)
                                              [a]'')
                    G[a]' = proj₁ ([G] ⊢Δ₁ ([ρσ] , [a]'))
                    G[a]₁' = proj₁ ([G] ⊢Δ₁ ([ρσ'] , [a]''))
                    G[a] = [G]' ρ ⊢Δ₁ [a]
                    G[a]'' = [G]'' ρ ⊢Δ₁
                                   (irrelevanceTerm' (PE.sym (wk-subst F))
                                                     (proj₁ ([F] ⊢Δ₁ [ρσ']))
                                                     ([F]'' ρ ⊢Δ₁)
                                                     [a]'')
                    [σG[a]≡σ'G[a]] = irrelevanceEq''
                                       (PE.sym (G-substWkLemma a σ G))
                                       (PE.sym (G-substWkLemma a σ' G))
                                       G[a]' G[a]
                                       (proj₂ ([G] ⊢Δ₁ ([ρσ] , [a]'))
                                              ([ρσ'] , [a]'')
                                              (consSubstSEq {t = a} {A = F}
                                                [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ'] [F] [a]'))
                    [G]₁ = proj₁ ([G] (⊢Δ₁ ∙ ⊢F₁')
                                      (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                    [G]₁' = irrelevanceΓ'
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (G-lamLemma G)) [G]₁
                    [G]₂ = proj₁ ([G] (⊢Δ₁ ∙ ⊢F₂')
                                      (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ']))
                    [G]₂' = irrelevanceΓ'
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (G-lamLemma G)) [G]₂
                    [t]' = irrelevanceTermΓ''
                             (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                             (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t))
                             [G]₁ [G]₁'
                             (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁')
                                         (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                    [t]'' = irrelevanceTermΓ''
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t))
                              [G]₂ [G]₂'
                              (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₂')
                                          (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ'])))
                    ⊢t = wellformedTerm [G]₁' [t]'
                    ⊢t' = wellformedTerm [G]₂' [t]''
                    t[a] = irrelevanceTerm''
                             (PE.sym (G-substWkLemma a σ G))
                             (PE.sym (G-substWkLemma a σ t)) G[a]' G[a]
                             (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]')))
                    t[a]' = irrelevanceTerm''
                              (PE.sym (G-substWkLemma a σ' G))
                              (PE.sym (G-substWkLemma a σ' t))
                              G[a]₁' G[a]''
                              (proj₁ ([t] ⊢Δ₁ ([ρσ'] , [a]'')))
                    [σlamt∘a≡σt[a]] = proj₂ (redSubstTerm (β-red ⊢F₁ ⊢t ⊢a)
                                                          G[a] t[a])
                    [σ't[a]≡σ'lamt∘a] =
                      convEqTerm₂ G[a] G[a]'' [σG[a]≡σ'G[a]]
                        (symEqTerm G[a]''
                           (proj₂ (redSubstTerm (β-red ⊢F₂ ⊢t' ⊢a')
                                                G[a]'' t[a]')))
                    [σt[a]≡σ't[a]] = irrelevanceEqTerm''
                                       (PE.sym (G-substWkLemma a σ t))
                                       (PE.sym (G-substWkLemma a σ' t))
                                       (PE.sym (G-substWkLemma a σ G))
                                       G[a]' G[a]
                                       (proj₂ ([t] ⊢Δ₁ ([ρσ] , [a]'))
                                              ([ρσ'] , [a]'')
                                              (consSubstSEq {t = a} {A = F}
                                                [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ'] [F] [a]'))
                in  transEqTerm G[a] [σlamt∘a≡σt[a]]
                                (transEqTerm G[a] [σt[a]≡σ't[a]]
                                             [σ't[a]≡σ'lamt∘a])
         in  Πₜ₌ (lam (subst (liftSubst σ) t)) (lam (subst (liftSubst σ') t))
                 (idRedTerm:*: (lam ⊢F ⊢t))
                 (idRedTerm:*: (conv (lam ⊢F' ⊢t')
                                     (sym (≅-eq (wellformedEq (proj₁ ([ΠFG] ⊢Δ [σ]))
                                                              [σΠFG≡σ'ΠFG])))))
                 lam lam
                 (≅-fun-ext ⊢F (lam ⊢F ⊢t)
                      (conv (lam ⊢F' ⊢t')
                            (sym (≅-eq (wellformedEq (proj₁ ([ΠFG] ⊢Δ [σ]))
                                              [σΠFG≡σ'ΠFG]))))
                      (wellformedTermEq
                        (proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ]))
                        (irrelevanceEqTerm'
                          (idWkLiftSubstLemma σ G)
                          ([G]' (T.step T.id) (⊢Δ ∙ ⊢F) neuVar)
                          (proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ]))
                          (σlamt∘a≡σ'lamt∘a (T.step T.id) (⊢Δ ∙ ⊢F) neuVar))))
                  (lamt ⊢Δ [σ])
                  (convTerm₂ (proj₁ ([ΠFG] ⊢Δ [σ]))
                             (proj₁ ([ΠFG] ⊢Δ [σ']))
                             [σΠFG≡σ'ΠFG]
                             (lamt ⊢Δ [σ']))
                  σlamt∘a≡σ'lamt∘a)

lemma4 : ∀ ρ σ a x → substComp (liftSubst σ)
      (purge (lift ρ) (consSubst idSubst a)) x
      PE.≡ consSubst (wkSubst ρ σ) a x
lemma4 ρ σ a zero = PE.refl
lemma4 ρ σ a (suc x) = PE.trans (subst-wk (σ x)) (PE.sym (wk2subst ρ (σ x)))


fun-extEqTerm : ∀ {f g F G Γ Δ σ l}
                ([Γ] : ⊩ₛ Γ)
                ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
                ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
              → let [ΠFG] = Πₛ {F} {G} [Γ] [F] [G] in
                Γ ∙ F ⊩ₛ⟨ l ⟩t' wk1 f ∘ var zero ≡ wk1 g ∘ var zero ∷ G
                             / [Γ] ∙ [F] / [G]
              → (⊢Δ   : ⊢ Δ)
                ([σ]  : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
              → Δ ⊩⟨ l ⟩ subst σ f ∷ Π subst σ F ▹ subst (liftSubst σ) G
                  / proj₁ ([ΠFG] ⊢Δ [σ])
              → Δ ⊩⟨ l ⟩ subst σ g ∷ Π subst σ F ▹ subst (liftSubst σ) G
                  / proj₁ ([ΠFG] ⊢Δ [σ])
              → Δ ⊩⟨ l ⟩ subst σ f ≡ subst σ g ∷ Π subst σ F ▹ subst (liftSubst σ) G
                  / proj₁ ([ΠFG] ⊢Δ [σ])
fun-extEqTerm {f} {g} {F} {G} {Γ} {Δ} {σ} [Γ] [F] [G] [f0≡g0] ⊢Δ [σ]
              (Πₜ f₁ [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁)
              (Πₜ g₁ [ ⊢t₁ , ⊢u₁ , d₁ ] funcG g≡g [g] [g]₁) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ ⊢t₁ , ⊢u₁ , d₁ ]
      [ΠFG] = Πₛ {F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Π F' G' D' ⊢F ⊢G A≡A [F]' [G]' G-ext = extractMaybeEmb (Π-elim [σΠFG])
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      σf0≡σg0 = wellformedTermEq [σG]
                                ([f0≡g0] (⊢Δ ∙ ⊢F)
                                         (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      σf0≡σg0' =
        PE.subst₂
          (λ x y → Δ ∙ subst σ F ⊢ x ≅ y ∷ subst (liftSubst σ) G)
          (PE.cong₂ _∘_ (PE.trans (subst-wk f) (PE.sym (wk-subst f))) PE.refl)
          (PE.cong₂ _∘_ (PE.trans (subst-wk g) (PE.sym (wk-subst g))) PE.refl)
          σf0≡σg0
  in  Πₜ₌ f₁ g₁ [d] [d'] funcF funcG
          (≅-fun-ext ⊢F ⊢t ⊢t₁ σf0≡σg0')
          (Πₜ f₁ [d] funcF f≡f [f] [f]₁)
          (Πₜ g₁ [d'] funcG g≡g [g] [g]₁)
          (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
             let [a]' = irrelevanceTerm'
                          (wk-subst F) ([F]' ρ ⊢Δ₁)
                          (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
                 fEq = PE.cong₂ _∘_ (PE.trans (subst-wk f) (PE.sym (wk-subst f))) PE.refl
                 gEq = PE.cong₂ _∘_ (PE.trans (subst-wk g) (PE.sym (wk-subst g))) PE.refl
                 GEq = PE.sym (PE.trans (subst-wk (subst (liftSubst σ) G))
                                        (PE.trans (substCompEq G)
                                                  (substEq (lemma4 (T.toWk ρ) σ a) G)))
             in  irrelevanceEqTerm'' fEq gEq GEq
                                     (proj₁ ([G] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ] , [a]')))
                                     ([G]' ρ ⊢Δ₁ [a])
                                     ([f0≡g0] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ] , [a]')))

fun-extₛ : ∀ {f g F G Γ l}
           ([Γ] : ⊩ₛ Γ)
           ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
         → let [ΠFG] = Πₛ {F} {G} [Γ] [F] [G] in
           Γ ⊩ₛ⟨ l ⟩t f ∷ Π F ▹ G / [Γ] / [ΠFG]
         → Γ ⊩ₛ⟨ l ⟩t g ∷ Π F ▹ G / [Γ] / [ΠFG]
         → Γ ∙ F ⊩ₛ⟨ l ⟩t' wk1 f ∘ var zero ≡ wk1 g ∘ var zero ∷ G
                        / [Γ] ∙ [F] / [G]
         → Γ ⊩ₛ⟨ l ⟩t' f ≡ g ∷ Π F ▹ G / [Γ] / [ΠFG]
fun-extₛ {f} {g} {F} {G} [Γ] [F] [G] [f] [g] [f0≡g0] {Δ} {σ} ⊢Δ [σ] =
  fun-extEqTerm {f} {g} {F} {G} [Γ] [F] [G] [f0≡g0] ⊢Δ [σ]
                (proj₁ ([f] ⊢Δ [σ])) (proj₁ ([g] ⊢Δ [σ]))
