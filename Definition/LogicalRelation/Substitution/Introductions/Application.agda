{-# OPTIONS --without-K #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Empty
open import Tools.Product

import Tools.PropositionalEquality as PE


appTerm' : ∀ {F G t u Γ l l' l''}
          ([F] : Γ ⊩⟨ l'' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / Π-intr [ΠFG])
          ([u] : Γ ⊩⟨ l'' ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm' {t = t} {Γ = Γ} [F] [G[u]] (noemb (Π F G D ⊢F ⊢G A≡A [F'] [G'] G-ext))
         (Πₜ f d funcF f≡f [f] [f]₁) [u] =
  let ΠFG≡ΠF'G' = whnfRed* (red D) Π
      F≡F' , G≡G' = Π-PE-injectivity ΠFG≡ΠF'G'
      F≡idF' = PE.trans F≡F' (PE.sym (wk-id _ 0))
      idG'ᵤ≡Gᵤ = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      idf∘u≡f∘u = (PE.cong (λ x → x ∘ _) (wk-id _ 0))
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' F≡idF' [F] ([F'] T.id ⊢Γ) [u]
      [f∘u] = irrelevanceTerm'' idG'ᵤ≡Gᵤ idf∘u≡f∘u
                                ([G'] T.id ⊢Γ [u]') [G[u]] ([f]₁ T.id ⊢Γ [u]')
      ⊢u = wellformedTerm [F] [u]
      d' = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x) (PE.sym ΠFG≡ΠF'G') (redₜ d)
  in  proj₁ (redSubst*Term (app-subst* d' ⊢u) [G[u]] [f∘u])
appTerm' [F] [G[u]] (emb 0<1 x) [t] [u] = appTerm' [F] [G[u]] x [t] [u]

appTerm : ∀ {F G t u Γ l l' l''}
          ([F] : Γ ⊩⟨ l'' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l'' ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm [F] [G[u]] [ΠFG] [t] [u] =
  let [t]' = irrelevanceTerm [ΠFG] (Π-intr (Π-elim [ΠFG])) [t]
  in  appTerm' [F] [G[u]] (Π-elim [ΠFG]) [t]' [u]

app-congTerm' : ∀ {F G t t' u u' Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
          ([t≡t'] : Γ ⊩⟨ l ⟩ t ≡ t' ∷ Π F ▹ G / Π-intr [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
          ([u'] : Γ ⊩⟨ l' ⟩ u' ∷ F / [F])
          ([u≡u'] : Γ ⊩⟨ l' ⟩ u ≡ u' ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ≡ t' ∘ u' ∷ G [ u ] / [G[u]]
app-congTerm' {F'} {G'} {t = t} {t' = t'} {Γ = Γ}
              [F] [G[u]] (noemb (Π F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext))
              (Πₜ₌ f g [ ⊢t , ⊢f , d ] [ ⊢t' , ⊢g , d' ] funcF funcG t≡u
                   (Πₜ f' [ _ , ⊢f' , d'' ] funcF' f≡f [f] [f]₁)
                   (Πₜ g' [ _ , ⊢g' , d''' ] funcG' g≡g [g] [g]₁) [t≡u])
              [a] [a'] [a≡a'] =
  let [ΠFG] = Π' F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext
      ΠFG≡ΠF'G' = whnfRed* (red D) Π
      F≡F' , G≡G' = Π-PE-injectivity ΠFG≡ΠF'G'
      f≡f' = whrDet*Term (d , functionWhnf funcF) (d'' , functionWhnf funcF')
      g≡g' = whrDet*Term (d' , functionWhnf funcG) (d''' , functionWhnf funcG')
      F≡wkidF' = PE.trans F≡F' (PE.sym (wk-id _ 0))
      t∘x≡wkidt∘x : {a b : Term} → U.wk id a Term.∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a 0)
      t∘x≡wkidt∘x' : {a : Term} → U.wk id g' Term.∘ a PE.≡ g ∘ a
      t∘x≡wkidt∘x' {a} = PE.cong (λ x → x ∘ a) (PE.trans (wk-id _ 0) (PE.sym g≡g'))
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ])
                               (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      wkidG₁[u']≡G[u'] = PE.cong (λ x → x [ _ ])
                                 (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [a]
      [u']' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [a']
      [u≡u']' = irrelevanceEqTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [a≡a']
      [G[u']] = irrelevance' wkidG₁[u']≡G[u'] ([G] T.id ⊢Γ [u']')
      [G[u≡u']] = irrelevanceEq'' wkidG₁[u]≡G[u] wkidG₁[u']≡G[u']
                                  ([G] T.id ⊢Γ [u]') [G[u]]
                                  (G-ext T.id ⊢Γ [u]' [u']' [u≡u']')
      [f'] : Γ ⊩⟨ _ ⟩ f' ∷ Π F' ▹ G' / [ΠFG]
      [f'] = Πₜ f' (idRedTerm:*: ⊢f') funcF' f≡f [f] [f]₁
      [g'] : Γ ⊩⟨ _ ⟩ g' ∷ Π F' ▹ G' / [ΠFG]
      [g'] = Πₜ g' (idRedTerm:*: ⊢g') funcG' g≡g [g] [g]₁
      [f∘u] = appTerm [F] [G[u]] [ΠFG]
                      (irrelevanceTerm'' PE.refl (PE.sym f≡f') [ΠFG] [ΠFG] [f'])
                      [a]
      [g∘u'] = appTerm [F] [G[u']] [ΠFG]
                       (irrelevanceTerm'' PE.refl (PE.sym g≡g') [ΠFG] [ΠFG] [g'])
                       [a']
      [tu≡t'u] = irrelevanceEqTerm'' t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                     ([G] T.id ⊢Γ [u]') [G[u]]
                                     ([t≡u] T.id ⊢Γ [u]')
      [t'u≡t'u'] = irrelevanceEqTerm'' t∘x≡wkidt∘x' t∘x≡wkidt∘x' wkidG₁[u]≡G[u]
                                       ([G] T.id ⊢Γ [u]') [G[u]]
                                       ([g] T.id ⊢Γ [u]' [u']' [u≡u']')
      d₁ = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x) (PE.sym ΠFG≡ΠF'G') d
      d₂ = PE.subst (λ x → Γ ⊢ t' ⇒* g ∷ x) (PE.sym ΠFG≡ΠF'G') d'
      [tu≡fu] = proj₂ (redSubst*Term (app-subst* d₁ (wellformedTerm [F] [a]))
                                     [G[u]] [f∘u])
      [gu'≡t'u'] = convEqTerm₂ [G[u]] [G[u']] [G[u≡u']]
                     (symEqTerm [G[u']]
                       (proj₂ (redSubst*Term (app-subst* d₂ (wellformedTerm [F] [a']))
                                             [G[u']] [g∘u'])))
  in  transEqTerm [G[u]] (transEqTerm [G[u]] [tu≡fu] [tu≡t'u])
                         (transEqTerm [G[u]] [t'u≡t'u'] [gu'≡t'u'])
app-congTerm' [F] [G[u]] (emb 0<1 x) [t≡t'] [u] [u'] [u≡u'] =
  app-congTerm' [F] [G[u]] x [t≡t'] [u] [u'] [u≡u']

app-congTerm : ∀ {F G t t' u u' Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t≡t'] : Γ ⊩⟨ l ⟩ t ≡ t' ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
          ([u'] : Γ ⊩⟨ l' ⟩ u' ∷ F / [F])
          ([u≡u'] : Γ ⊩⟨ l' ⟩ u ≡ u' ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ≡ t' ∘ u' ∷ G [ u ] / [G[u]]
app-congTerm [F] [G[u]] [ΠFG] [t≡t'] =
  let [t≡t']' = irrelevanceEqTerm [ΠFG] (Π-intr (Π-elim [ΠFG])) [t≡t']
  in  app-congTerm' [F] [G[u]] (Π-elim [ΠFG]) [t≡t']'

appₛ : ∀ {F G t u Γ}
       ([Γ] : ⊩ₛ Γ)
       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
       ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
       ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ Π F ▹ G / [Γ] / [ΠFG])
       ([u] : Γ ⊩ₛ⟨ ¹ ⟩t u ∷ F / [Γ] / [F])
     → Γ ⊩ₛ⟨ ¹ ⟩t t ∘ u ∷ G [ u ] / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appₛ {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]' = irrelevance' (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm' (PE.sym (singleSubstLift G u))
                       [σG[u]]' [σG[u]]
                       (appTerm [σF] [σG[u]]' [σΠFG] [σt] [σu])
  ,   (λ [σ'] [σ≡σ'] →
         let [σu'] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ']))
                               (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ'])
                               (proj₁ ([u] ⊢Δ [σ']))
         in  irrelevanceEqTerm' (PE.sym (singleSubstLift G u))
                                [σG[u]]' [σG[u]]
                                (app-congTerm [σF] [σG[u]]' [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ'])
                                              [σu] [σu']
                                              (proj₂ ([u] ⊢Δ [σ]) [σ'] [σ≡σ'])))

app-congₛ : ∀ {F G t u a b Γ}
            ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
            ([t≡u] : Γ ⊩ₛ⟨ ¹ ⟩t' t ≡ u ∷ Π F ▹ G / [Γ] / [ΠFG])
            ([a] : Γ ⊩ₛ⟨ ¹ ⟩t a ∷ F / [Γ] / [F])
            ([b] : Γ ⊩ₛ⟨ ¹ ⟩t b ∷ F / [Γ] / [F])
            ([a≡b] : Γ ⊩ₛ⟨ ¹ ⟩t' a ≡ b ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ ¹ ⟩t' t ∘ a ≡ u ∘ b ∷ G [ a ] / [Γ]
              / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congₛ {F} {G} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]' = irrelevance' (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm' (PE.sym (singleSubstLift G a)) [G[a]]' [G[a]]
                         (app-congTerm [σF] [G[a]]' [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]))
