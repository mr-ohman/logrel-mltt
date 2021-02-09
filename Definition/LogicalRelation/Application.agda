{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (id)
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Helper function for application of specific type derivations.
appTerm′ : ∀ {F G t u l l′ l″}
          ([F] : Γ ⊩⟨ l″ ⟩ F)
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩B⟨ BΠ ⟩ Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / B-intr BΠ [ΠFG])
          ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm′ {Γ = Γ} {t = t} [F] [G[u]] (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F′] [G′] G-ext))
         (Πₜ f d funcF f≡f [f] [f]₁) [u] =
  let ΠFG≡ΠF′G′ = whnfRed* (red D) Πₙ
      F≡F′ , G≡G′ = B-PE-injectivity BΠ ΠFG≡ΠF′G′
      F≡idF′ = PE.trans F≡F′ (PE.sym (wk-id _))
      idG′ᵤ≡Gᵤ = PE.cong (λ x → x [ _ ]) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      idf∘u≡f∘u = (PE.cong (λ x → x ∘ _) (wk-id _))
      ⊢Γ = wf ⊢F
      [u]′ = irrelevanceTerm′ F≡idF′ [F] ([F′] id ⊢Γ) [u]
      [f∘u] = irrelevanceTerm″ idG′ᵤ≡Gᵤ idf∘u≡f∘u
                                ([G′] id ⊢Γ [u]′) [G[u]] ([f]₁ id ⊢Γ [u]′)
      ⊢u = escapeTerm [F] [u]
      d′ = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x) (PE.sym ΠFG≡ΠF′G′) (redₜ d)
  in  proj₁ (redSubst*Term (app-subst* d′ ⊢u) [G[u]] [f∘u])
appTerm′ [F] [G[u]] (emb 0<1 x) [t] [u] = appTerm′ [F] [G[u]] x [t] [u]

-- Application of reducible terms.
appTerm : ∀ {F G t u l l′ l″}
          ([F] : Γ ⊩⟨ l″ ⟩ F)
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm [F] [G[u]] [ΠFG] [t] [u] =
  let [t]′ = irrelevanceTerm [ΠFG] (B-intr BΠ (Π-elim [ΠFG])) [t]
  in  appTerm′ [F] [G[u]] (Π-elim [ΠFG]) [t]′ [u]

-- Helper function for application congruence of specific type derivations.
app-congTerm′ : ∀ {n} {Γ : Con Term n} {F G t t′ u u′ l l′}
          ([F] : Γ ⊩⟨ l′ ⟩ F)
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩B⟨ BΠ ⟩ Π F ▹ G)
          ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Π F ▹ G / B-intr BΠ [ΠFG])
          ([u] : Γ ⊩⟨ l′ ⟩ u ∷ F / [F])
          ([u′] : Γ ⊩⟨ l′ ⟩ u′ ∷ F / [F])
          ([u≡u′] : Γ ⊩⟨ l′ ⟩ u ≡ u′ ∷ F / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ≡ t′ ∘ u′ ∷ G [ u ] / [G[u]]
app-congTerm′ {n} {Γ} {F′} {G′} {t = t} {t′ = t′}
              [F] [G[u]] (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext))
              (Πₜ₌ f g [ ⊢t , ⊢f , d ] [ ⊢t′ , ⊢g , d′ ] funcF funcG t≡u
                   (Πₜ f′ [ _ , ⊢f′ , d″ ] funcF′ f≡f [f] [f]₁)
                   (Πₜ g′ [ _ , ⊢g′ , d‴ ] funcG′ g≡g [g] [g]₁) [t≡u])
              [a] [a′] [a≡a′] =
  let [ΠFG] = Πᵣ′ F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext
      ΠFG≡ΠF′G′ = whnfRed* (red D) Πₙ
      F≡F′ , G≡G′ = B-PE-injectivity BΠ ΠFG≡ΠF′G′
      f≡f′ = whrDet*Term (d , functionWhnf funcF) (d″ , functionWhnf funcF′)
      g≡g′ = whrDet*Term (d′ , functionWhnf funcG) (d‴ , functionWhnf funcG′)
      F≡wkidF′ = PE.trans F≡F′ (PE.sym (wk-id _))
      t∘x≡wkidt∘x : {a b : Term n} → wk id a ∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a)
      t∘x≡wkidt∘x′ : {a : Term n} → wk id g′ ∘ a PE.≡ g ∘ a
      t∘x≡wkidt∘x′ {a} = PE.cong (λ x → x ∘ a) (PE.trans (wk-id _) (PE.sym g≡g′))
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ])
                               (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      wkidG₁[u′]≡G[u′] = PE.cong (λ x → x [ _ ])
                                 (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      ⊢Γ = wf ⊢F
      [u]′ = irrelevanceTerm′ F≡wkidF′ [F] ([F]₁ id ⊢Γ) [a]
      [u′]′ = irrelevanceTerm′ F≡wkidF′ [F] ([F]₁ id ⊢Γ) [a′]
      [u≡u′]′ = irrelevanceEqTerm′ F≡wkidF′ [F] ([F]₁ id ⊢Γ) [a≡a′]
      [G[u′]] = irrelevance′ wkidG₁[u′]≡G[u′] ([G] id ⊢Γ [u′]′)
      [G[u≡u′]] = irrelevanceEq″ wkidG₁[u]≡G[u] wkidG₁[u′]≡G[u′]
                                  ([G] id ⊢Γ [u]′) [G[u]]
                                  (G-ext id ⊢Γ [u]′ [u′]′ [u≡u′]′)
      [f′] : Γ ⊩⟨ _ ⟩ f′ ∷ Π F′ ▹ G′ / [ΠFG]
      [f′] = Πₜ f′ (idRedTerm:*: ⊢f′) funcF′ f≡f [f] [f]₁
      [g′] : Γ ⊩⟨ _ ⟩ g′ ∷ Π F′ ▹ G′ / [ΠFG]
      [g′] = Πₜ g′ (idRedTerm:*: ⊢g′) funcG′ g≡g [g] [g]₁
      [f∘u] = appTerm [F] [G[u]] [ΠFG]
                      (irrelevanceTerm″ PE.refl (PE.sym f≡f′) [ΠFG] [ΠFG] [f′])
                      [a]
      [g∘u′] = appTerm [F] [G[u′]] [ΠFG]
                       (irrelevanceTerm″ PE.refl (PE.sym g≡g′) [ΠFG] [ΠFG] [g′])
                       [a′]
      [tu≡t′u] = irrelevanceEqTerm″ t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                     ([G] id ⊢Γ [u]′) [G[u]]
                                     ([t≡u] id ⊢Γ [u]′)
      [t′u≡t′u′] = irrelevanceEqTerm″ t∘x≡wkidt∘x′ t∘x≡wkidt∘x′ wkidG₁[u]≡G[u]
                                       ([G] id ⊢Γ [u]′) [G[u]]
                                       ([g] id ⊢Γ [u]′ [u′]′ [u≡u′]′)
      d₁ = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x) (PE.sym ΠFG≡ΠF′G′) d
      d₂ = PE.subst (λ x → Γ ⊢ t′ ⇒* g ∷ x) (PE.sym ΠFG≡ΠF′G′) d′
      [tu≡fu] = proj₂ (redSubst*Term (app-subst* d₁ (escapeTerm [F] [a]))
                                     [G[u]] [f∘u])
      [gu′≡t′u′] = convEqTerm₂ [G[u]] [G[u′]] [G[u≡u′]]
                     (symEqTerm [G[u′]]
                       (proj₂ (redSubst*Term (app-subst* d₂ (escapeTerm [F] [a′]))
                                             [G[u′]] [g∘u′])))
  in  transEqTerm [G[u]] (transEqTerm [G[u]] [tu≡fu] [tu≡t′u])
                         (transEqTerm [G[u]] [t′u≡t′u′] [gu′≡t′u′])
app-congTerm′ [F] [G[u]] (emb 0<1 x) [t≡t′] [u] [u′] [u≡u′] =
  app-congTerm′ [F] [G[u]] x [t≡t′] [u] [u′] [u≡u′]

-- Application congruence of reducible terms.
app-congTerm : ∀ {F G t t′ u u′ l l′}
          ([F] : Γ ⊩⟨ l′ ⟩ F)
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l′ ⟩ u ∷ F / [F])
          ([u′] : Γ ⊩⟨ l′ ⟩ u′ ∷ F / [F])
          ([u≡u′] : Γ ⊩⟨ l′ ⟩ u ≡ u′ ∷ F / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ≡ t′ ∘ u′ ∷ G [ u ] / [G[u]]
app-congTerm [F] [G[u]] [ΠFG] [t≡t′] =
  let [t≡t′]′ = irrelevanceEqTerm [ΠFG] (B-intr BΠ (Π-elim [ΠFG])) [t≡t′]
  in  app-congTerm′ [F] [G[u]] (Π-elim [ΠFG]) [t≡t′]′
