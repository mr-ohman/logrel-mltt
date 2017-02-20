open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.SingleSubst {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE


substS : ∀ {F G t Γ l} ([Γ] : ⊩ₛ Γ)
         ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
         ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
       → Γ ⊩ₛ⟨ l ⟩ G [ t ] / [Γ]
substS {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let Geq = PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G))
      G[t] = proj₁ ([G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ]))))
      G[t]' = irrelevance' Geq G[t]
  in  G[t]'
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         irrelevanceEq'' Geq
                         (PE.sym (PE.trans (substCompEq G)
                                           (substEq substConcatSingleton' G)))
                         G[t] G[t]'
                         (proj₂ ([G] ⊢Δ
                                     ([σ] , proj₁ ([t] ⊢Δ [σ])))
                                     ([σ'] , proj₁ ([t] ⊢Δ [σ']))
                                     (([σ≡σ'] , (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ'])))))

substSEq : ∀ {F F' G G' t t' Γ l} ([Γ] : ⊩ₛ Γ)
           ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
           ([F'] : Γ ⊩ₛ⟨ l ⟩ F' / [Γ])
           ([F≡F'] : Γ ⊩ₛ⟨ l ⟩ F ≡ F' / [Γ] / [F])
           ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([G'] : Γ ∙ F' ⊩ₛ⟨ l ⟩ G' / [Γ] ∙ [F'])
           ([G≡G'] : Γ ∙ F ⊩ₛ⟨ l ⟩ G ≡ G' / [Γ] ∙ [F] / [G])
           ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
           ([t'] : Γ ⊩ₛ⟨ l ⟩t t' ∷ F' / [Γ] / [F'])
           ([t≡t'] : Γ ⊩ₛ⟨ l ⟩t' t ≡ t' ∷ F / [Γ] / [F])
         → Γ ⊩ₛ⟨ l ⟩ G [ t ] ≡ G' [ t' ] / [Γ]
                   / substS {F} {G} {t} [Γ] [F] [G] [t]
substSEq {F} {F'} {G} {G'} {t} {t'}
         [Γ] [F] [F'] [F≡F'] [G] [G'] [G≡G'] [t] [t'] [t≡t'] {σ = σ} ⊢Δ [σ] =
  let Geq = PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G))
      G'eq = PE.sym (PE.trans (substCompEq G') (substEq substConcatSingleton' G'))
      G[t] = (proj₁ ([G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ])))))
      G[t]' = irrelevance' Geq G[t]
      [t]' = convₛ {t} {F} {F'} [Γ] [F] [F'] [F≡F'] [t]
      G'[t] = (proj₁ ([G'] ⊢Δ ([σ] , proj₁ ([t]' ⊢Δ [σ]))))
      G[t]≡G'[t] = irrelevanceEq' Geq G[t] G[t]'
                                  ([G≡G'] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G'[t]≡G'[t'] = irrelevanceEq'' PE.refl G'eq G'[t] G'[t]
                       (proj₂ ([G'] ⊢Δ ([σ] , proj₁ ([t]' ⊢Δ [σ])))
                              ([σ] , proj₁ ([t'] ⊢Δ [σ]))
                              (reflSubst [Γ] ⊢Δ [σ] ,
                                convEqₛ {t} {t'} {F} {F'}
                                        [Γ] [F] [F'] [F≡F'] [t≡t'] ⊢Δ [σ]))
      G'[t'] = (proj₁ ([G'] ⊢Δ ([σ] , proj₁ ([t'] ⊢Δ [σ]))))
      G'[t']' = irrelevance' G'eq G'[t']
  in  transEq G[t]' G'[t] G'[t']' G[t]≡G'[t] G'[t]≡G'[t']

substSTerm : ∀ {F G t f Γ l} ([Γ] : ⊩ₛ Γ)
             ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
             ([f] : Γ ∙ F ⊩ₛ⟨ l ⟩t f ∷ G / [Γ] ∙ [F] / [G])
             ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
           → Γ ⊩ₛ⟨ l ⟩t f [ t ] ∷ G [ t ] / [Γ]
                      / substS {F} {G} {t} [Γ] [F] [G] [t]
substSTerm {F} {G} {t} {f} [Γ] [F] [G] [f] [t] {σ = σ} ⊢Δ [σ] =
  let prfG = PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G))
      prff = PE.sym (PE.trans (substCompEq f) (substEq substConcatSingleton' f))
      G[t] = proj₁ ([G] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G[t]' = irrelevance' prfG G[t]
      f[t] = proj₁ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      f[t]' = irrelevanceTerm'' prfG prff G[t] G[t]' f[t]
  in  f[t]'
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         irrelevanceEqTerm''
           prff
           (PE.sym (PE.trans (substCompEq f) (substEq substConcatSingleton' f)))
           prfG G[t] G[t]'
           (proj₂ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
                  ([σ'] , proj₁ ([t] ⊢Δ [σ']))
                  ([σ≡σ'] , proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ'])))

lemma3 : ∀ {G t σ} →
         subst (consSubst (λ n → σ (suc n)) (subst σ t)) G PE.≡
         subst σ (subst (consSubst (λ x → var (suc x)) t) G)
lemma3 {G} {t} {σ} = PE.trans (substEq
                                (λ { zero → PE.refl
                                ; (suc x) → PE.refl }) G)
                              (PE.sym (substCompEq G))

subst↑S : ∀ {F G t Γ l} ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ∙ F ⊩ₛ⟨ l ⟩t t ∷ wk1 F / [Γ] ∙ [F]
                              / wk1ₛ {F} {F} [Γ] [F] [F])
        → Γ ∙ F ⊩ₛ⟨ l ⟩ G [ t ]↑ / [Γ] ∙ [F]
subst↑S {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ₛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]' = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t] ⊢Δ [σ]))
      G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ
                               (proj₁ [σ] , [t]'))
      G[t]' = irrelevance' (lemma3 {G} {t} {σ}) G[t]
  in  G[t]'
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         let [σ't] = irrelevanceTerm' (subst-wk F)
                                      (proj₁ ([wk1F] {σ = σ'} ⊢Δ [σ']))
                                      (proj₁ ([F] ⊢Δ (proj₁ [σ'])))
                                      (proj₁ ([t] ⊢Δ [σ']))
             [σt≡σ't] = irrelevanceEqTerm' (subst-wk F) [σwk1F] [σwk1F]'
                                           (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ'])
             [σG[t]≡σ'G[t]] = proj₂ ([G] ⊢Δ (proj₁ [σ] , [t]'))
                                    (proj₁ [σ'] , [σ't])
                                    (proj₁ [σ≡σ'] , [σt≡σ't])
         in irrelevanceEq'' (lemma3 {G} {t} {σ}) (lemma3 {G} {t} {σ'})
                            G[t] G[t]' [σG[t]≡σ'G[t]])

subst↑SEq : ∀ {F G G' t t' Γ l} ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([G'] : Γ ∙ F ⊩ₛ⟨ l ⟩ G' / [Γ] ∙ [F])
            ([G≡G'] : Γ ∙ F ⊩ₛ⟨ l ⟩ G ≡ G' / [Γ] ∙ [F] / [G])
            ([t] : Γ ∙ F ⊩ₛ⟨ l ⟩t t ∷ wk1 F / [Γ] ∙ [F]
                                / wk1ₛ {F} {F} [Γ] [F] [F])
            ([t'] : Γ ∙ F ⊩ₛ⟨ l ⟩t t' ∷ wk1 F / [Γ] ∙ [F]
                                 / wk1ₛ {F} {F} [Γ] [F] [F])
            ([t≡t'] : Γ ∙ F ⊩ₛ⟨ l ⟩t' t ≡ t' ∷ wk1 F / [Γ] ∙ [F]
                                   / wk1ₛ {F} {F} [Γ] [F] [F])
          → Γ ∙ F ⊩ₛ⟨ l ⟩ G [ t ]↑ ≡ G' [ t' ]↑ / [Γ] ∙ [F]
                        / subst↑S {F} {G} {t} [Γ] [F] [G] [t]
subst↑SEq {F} {G} {G'} {t} {t'}
          [Γ] [F] [G] [G'] [G≡G'] [t] [t'] [t≡t'] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ₛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]' = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t] ⊢Δ [σ]))
      [t']' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t'] ⊢Δ [σ]))
      [t≡t']' = irrelevanceEqTerm' (subst-wk F) [σwk1F] [σwk1F]' ([t≡t'] ⊢Δ [σ])
      G[t] = proj₁ ([G] ⊢Δ (proj₁ [σ] , [t]'))
      G[t]' = irrelevance' (lemma3 {G} {t} {σ}) G[t]
      G'[t] = proj₁ ([G'] ⊢Δ (proj₁ [σ] , [t]'))
      G'[t]' = irrelevance' (lemma3 {G'} {t} {σ}) G'[t]
      G'[t'] = proj₁ ([G'] ⊢Δ (proj₁ [σ] , [t']'))
      G'[t']' = irrelevance' (lemma3 {G'} {t'} {σ}) G'[t']
      G[t]≡G'[t] = irrelevanceEq'' (lemma3 {G} {t} {σ}) (lemma3 {G'} {t} {σ})
                                   G[t] G[t]' ([G≡G'] ⊢Δ (proj₁ [σ] , [t]'))
      G'[t]≡G'[t'] = irrelevanceEq'' (lemma3 {G'} {t} {σ})
                                     (lemma3 {G'} {t'} {σ})
                                     G'[t] G'[t]'
                                     (proj₂ ([G'] ⊢Δ (proj₁ [σ] , [t]'))
                                            (proj₁ [σ] , [t']')
                                            (reflSubst [Γ] ⊢Δ (proj₁ [σ]) , [t≡t']'))
  in  transEq G[t]' G'[t]' G'[t']' G[t]≡G'[t] G'[t]≡G'[t']

substSΠ₁' : ∀ {F G t Γ l l'}
           ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
           ([F] : Γ ⊩⟨ l' ⟩ F)
           ([t] : Γ ⊩⟨ l' ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]
substSΠ₁' {t = t} (noemb (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [F]₁ [t] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      Feq = PE.trans F≡F' (PE.sym (wk-id _ 0))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      ⊢Γ = wf (wellformed [F]₁)
      [t]' = irrelevanceTerm' Feq [F]₁ ([F] T.id ⊢Γ) [t]
  in  irrelevance' Geq ([G] T.id ⊢Γ [t]')
substSΠ₁' (emb 0<1 x) [F]₁ [t] = emb 0<1 (substSΠ₁' x [F]₁ [t])

substSΠ₁ : ∀ {F G t Γ l l'}
           ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
           ([F] : Γ ⊩⟨ l' ⟩ F)
           ([t] : Γ ⊩⟨ l' ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]
substSΠ₁ [ΠFG] [F] [t] = substSΠ₁' (Π-elim [ΠFG]) [F] [t]

substSΠ₂' : ∀ {F F' G G' t t' Γ l l' l''}
           ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
           ([ΠFG≡ΠF'G'] : Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π F' ▹ G' / Π-intr [ΠFG])
           ([F] : Γ ⊩⟨ l' ⟩ F)
           ([F'] : Γ ⊩⟨ l' ⟩ F')
           ([t] : Γ ⊩⟨ l' ⟩ t ∷ F / [F])
           ([t'] : Γ ⊩⟨ l' ⟩ t' ∷ F' / [F'])
           ([t≡t'] : Γ ⊩⟨ l' ⟩ t ≡ t' ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l'' ⟩ G [ t ])
           ([G'[t']] : Γ ⊩⟨ l'' ⟩ G' [ t' ])
         → Γ ⊩⟨ l'' ⟩ G [ t ] ≡ G' [ t' ] / [G[t]]
substSΠ₂' (noemb (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext))
          (Π₌ F'' G'' D' A≡B [F≡F'] [G≡G'])
          [F]₁ [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      F'≡F'' , G'≡G'' = Π-PE-injectivity (whnfRed*' D' Π)
      Feq = PE.trans F≡F' (PE.sym (wk-id _ 0))
      F'eq = PE.trans F'≡F'' (PE.sym (wk-id _ 0))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      Geq' = PE.cong (λ x → x [ _ ]) (PE.trans G'≡G'' (PE.sym (wk-id _ 1)))
      ⊢Γ = wf (wellformed [F]₁)
      [t]' = irrelevanceTerm' Feq [F]₁ ([F] T.id ⊢Γ) [t]
      [t']' = convTerm₂' F'eq ([F] T.id ⊢Γ) [F'] ([F≡F'] T.id ⊢Γ) [t']
      [t≡t']' = irrelevanceEqTerm' Feq [F]₁ ([F] T.id ⊢Γ) [t≡t']
      [Gt≡Gt'] = G-ext T.id ⊢Γ [t]' [t']' [t≡t']'
      [Gt'≡G't'] = [G≡G'] T.id ⊢Γ [t']'
  in  irrelevanceEq' Geq ([G] T.id ⊢Γ [t]') [G[t]]
        (transEq' PE.refl Geq' ([G] T.id ⊢Γ [t]') ([G] T.id ⊢Γ [t']')
                  [G'[t']] [Gt≡Gt'] [Gt'≡G't'])
substSΠ₂' (emb 0<1 x) = substSΠ₂' x

substSΠ₂ : ∀ {F F' G G' t t' Γ l l' l''}
           ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
           ([ΠFG≡ΠF'G'] : Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π F' ▹ G' / [ΠFG])
           ([F] : Γ ⊩⟨ l' ⟩ F)
           ([F'] : Γ ⊩⟨ l' ⟩ F')
           ([t] : Γ ⊩⟨ l' ⟩ t ∷ F / [F])
           ([t'] : Γ ⊩⟨ l' ⟩ t' ∷ F' / [F'])
           ([t≡t'] : Γ ⊩⟨ l' ⟩ t ≡ t' ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l'' ⟩ G [ t ])
           ([G'[t']] : Γ ⊩⟨ l'' ⟩ G' [ t' ])
         → Γ ⊩⟨ l'' ⟩ G [ t ] ≡ G' [ t' ] / [G[t]]
substSΠ₂ [ΠFG] [ΠFG≡ΠF'G'] =
  let [ΠFG≡ΠF'G']' = irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠF'G']
  in  substSΠ₂' (Π-elim [ΠFG]) [ΠFG≡ΠF'G']'

substSΠ : ∀ {F G t Γ l}
          ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([ΠFG] : Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ])
          ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
        → Γ ⊩ₛ⟨ l ⟩ G [ t ] / [Γ]
substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ] =
  let [σG[t]] = substSΠ₁ (proj₁ ([ΠFG] ⊢Δ [σ])) (proj₁ ([F] ⊢Δ [σ]))
                         (proj₁ ([t] ⊢Δ [σ]))
      [σG[t]]' = irrelevance' (PE.sym (singleSubstLift G t))
                          [σG[t]]
  in  [σG[t]]'
  ,   (λ [σ'] [σ≡σ'] →
         irrelevanceEq'' (PE.sym (singleSubstLift G t))
                         (PE.sym (singleSubstLift G t))
                         [σG[t]] [σG[t]]'
                         (substSΠ₂ (proj₁ ([ΠFG] ⊢Δ [σ]))
                                   (proj₂ ([ΠFG] ⊢Δ [σ]) [σ'] [σ≡σ'])
                                   (proj₁ ([F] ⊢Δ [σ])) (proj₁ ([F] ⊢Δ [σ']))
                                   (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ']))
                                   (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ']) [σG[t]]
                                   (substSΠ₁ (proj₁ ([ΠFG] ⊢Δ [σ']))
                                             (proj₁ ([F] ⊢Δ [σ']))
                                             (proj₁ ([t] ⊢Δ [σ'])))))

substSΠEq : ∀ {F G t u Γ l}
            ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ])
            ([t]   : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
            ([u]   : Γ ⊩ₛ⟨ l ⟩t u ∷ F / [Γ] / [F])
            ([t≡u] : Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ l ⟩ G [ t ] ≡ G [ u ] / [Γ]
                    / substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t]
substSΠEq {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] [t≡u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Π F' G' D' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext' = extractMaybeEmb (Π-elim [σΠFG])
      F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D') Π)
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σt]' = irrelevanceTerm' (PE.trans F≡F' (PE.sym (wk-id F' 0)))
                               [σF] ([F]' T.id ⊢Δ) [σt]
      [σu]' = irrelevanceTerm' (PE.trans F≡F' (PE.sym (wk-id F' 0)))
                               [σF] ([F]' T.id ⊢Δ) [σu]
      [σt≡σu] = [t≡u] ⊢Δ [σ]
      [G[t]] = irrelevance' (PE.cong (λ x → x [ subst σ t ])
                                     (PE.trans (wk-id G' 1) (PE.sym G≡G')))
                            ([G]' T.id ⊢Δ [σt]')
      [G[u]] = irrelevance' (PE.cong (λ x → x [ subst σ u ])
                                     (PE.trans (wk-id G' 1) (PE.sym G≡G')))
                            ([G]' T.id ⊢Δ [σu]')
  in  irrelevanceEq'' (PE.sym (singleSubstLift G t))
                      (PE.sym (singleSubstLift G u))
                      [G[t]]
                      (proj₁ (substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ]))
                      (substSΠ₂ {subst σ F} {subst σ F}
                                {subst (liftSubst σ) G}
                                {subst (liftSubst σ) G}
                                (proj₁ ([ΠFG] ⊢Δ [σ]))
                                (reflEq (proj₁ ([ΠFG] ⊢Δ [σ])))
                                [σF] [σF] [σt] [σu] [σt≡σu] [G[t]] [G[u]])
