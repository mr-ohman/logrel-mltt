{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Pi {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    F : Term n
    G : Term (1+ n)
    Γ : Con Term n

-- Validity of W.
⟦_⟧ᵛ : ∀ W {n} {Γ : Con Term n} {F G l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
   → Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]
   → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G / [Γ]
⟦ W ⟧ᵛ {n} {Γ} {F} {G} {l} [Γ] [F] [G] {k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢ΠF▹G = ⟦ W ⟧ⱼ ⊢F [σ] ▹ ⊢G [σ]
      [G]a : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G)
               (λ [Aσ] →
               {σ′ : Subst m (1+ n)} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G / [Aσ])
      [G]a {_} {ρ} a [ρ] ⊢Δ₁ [a] = ([G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a]))
      [G]a′ : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
            → Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F
                 / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))
            → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ]
      [G]a′ a ρ ⊢Δ₁ [a] = irrelevance′ (PE.sym (singleSubstWkComp a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in Bᵣ′ W (subst σ F) (subst (liftSubst σ) G)
         (PE.subst
           (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G)
           (PE.sym (B-subst _ W F G))
           (idRed:*: ⊢ΠF▹G))
         (⊢F [σ]) (⊢G [σ])
         (≅-W-cong W (⊢F [σ]) ⊢F≡F ⊢G≡G)
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {_} {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
            let [a]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a]
            in  [G]a′ a [ρ] ⊢Δ₁ [a]′)
         (λ {_} {ρ} {Δ₁} {a} {b} [ρ] ⊢Δ₁ [a] [b] [a≡b] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [b]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                [a≡b]′ = irrelevanceEqTerm′
                           (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                           (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
            in  irrelevanceEq″
                  (PE.sym (singleSubstWkComp a σ G))
                  (PE.sym (singleSubstWkComp b σ G))
                  (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                  ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                  (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                         ([ρσ] , [b]′)
                         (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′)))
  ,  (λ {σ′} [σ′] [σ≡σ′] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ subst σ F))
                                 (wk-subst F) here)
            [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ′]
            [F][wk1σ] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
            [F][wk1σ′] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ′])
            var0′ = conv var0
                         (≅-eq (escapeEq [F][wk1σ]
                                             (proj₂ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
                                                    [wk1σ′] [wk1σ≡wk1σ′])))
        in  B₌ (subst σ′ F) (subst (liftSubst σ′) G)
               (PE.subst
                 (λ x → Δ ⊢ x ⇒* ⟦ W ⟧ subst σ′ F ▹ subst (liftSubst σ′) G)
                 (PE.sym (B-subst _ W F G))
                 (id (⟦ W ⟧ⱼ ⊢F [σ′] ▹ ⊢G [σ′])))
               (≅-W-cong W (⊢F [σ])
                       (escapeEq (proj₁ ([F] ⊢Δ [σ]))
                                    (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
                       (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                         ([wk1σ′] , neuTerm [F][wk1σ′] (var x0) var0′ (~-var var0′))
                         ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                           (var x0) (var x0) var0 var0 (~-var var0)))))
               (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
               (λ {_} {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                      [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                      [a]′ = irrelevanceTerm′ (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      [a]″ = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        (proj₁ ([F] ⊢Δ₁ [ρσ′]))
                                        (proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ′]
                                               (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′]))
                                        [a]′
                      [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′])
                                                [F] [a]′
                  in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                      (PE.sym (singleSubstWkComp a σ′ G))
                                      (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                                      ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                                      (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                                             (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′] , [a]″)
                                             [ρσa≡ρσ′a])))

-- Validity of W-congruence.
W-congᵛ : ∀ {F G H E l} W
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
          ([E] : Γ ∙ H ⊩ᵛ⟨ l ⟩ E / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
          ([G≡E] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ E / [Γ] ∙ [F] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E / [Γ] / ⟦ W ⟧ᵛ {F = F} {G} [Γ] [F] [G]
W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} BΠ [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = ⟦ BΠ ⟧ᵛ {F = F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      l′ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  B₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (Πⱼ ⊢σH ▹ ⊢σE))
         (≅-Π-cong ⊢σF ⊢σF≡σH ⊢σG≡σE)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst F)
                        eqB = PE.sym (wk-subst H)
                        p = proj₁ ([F] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (subst σ F)
                        wut = [F]′ ρ ⊢Δ₁
                        A≡B = [F≡H] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)
         (λ {_} {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F)
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E))
                                (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ]))

W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} BΣ [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = ⟦ BΣ ⟧ᵛ {F = F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      l′ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Σ-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  B₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (Σⱼ ⊢σH ▹ ⊢σE))
         (≅-Σ-cong ⊢σF ⊢σF≡σH ⊢σG≡σE)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst F)
                        eqB = PE.sym (wk-subst H)
                        p = proj₁ ([F] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (subst σ F)
                        wut = [F]′ ρ ⊢Δ₁
                        A≡B = [F≡H] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)
         (λ {_} {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F)
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E))
                                (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ]))

-- Validity of ⟦ W ⟧ as a term.
Wᵗᵛ : ∀ {Γ : Con Term n} {F G} W ([Γ] : ⊩ᵛ_ {n} Γ)
      ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
      ([U] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ]
    → Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F] / (λ {_} {Δ} {σ} → [U] {Δ = Δ} {σ})
    → Γ ⊩ᵛ⟨ ¹ ⟩ ⟦  W ⟧ F ▹ G ∷ U / [Γ] / Uᵛ [Γ]
Wᵗᵛ {Γ = Γ} {F} {G} W [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      ⊢Fₜ = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ)
                               (reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ])))
      ⊢Gₜ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      ⊢G≡Gₜ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                               (reflEqTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ])))
      [F]₀ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [Fₜ]
      [Gₜ]′ = S.irrelevanceTerm {A = U} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {_} {Δ} {σ} → [U] {Δ = Δ} {σ})
                                (λ {_} {Δ} {σ} → Uᵛ (_∙_ {A = F} [Γ] [F]₀) {Δ = Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {A = G} (_∙_ {A = F} [Γ] [F]₀)
                   (λ {_} {Δ} {σ} → Uᵛ (_∙_ {A = F} [Γ] [F]₀) {Δ = Δ} {σ})
                   (λ {_} {Δ} {σ} → [Gₜ]′ {Δ = Δ} {σ})
      [ΠFG] = (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ]
  in  Uₜ (⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G)
         (PE.subst (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G ∷ U) (PE.sym (B-subst σ W F G)) (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ ▹ ⊢Gₜ)))
         ⟦ W ⟧-type (≅ₜ-W-cong W ⊢F ⊢F≡Fₜ ⊢G≡Gₜ) (proj₁ [ΠFG])
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F [σ′]
             var0 = conv (var (⊢Δ ∙ ⊢F)
                         (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ subst σ F))
                                   (wk-subst F) here))
                    (≅-eq (escapeEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                        (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ′]
                                               (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′]))))
             [liftσ′]′ = [wk1σ′]
                       , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ′])) (var x0)
                                 var0 (~-var var0)
             ⊢F′ = escape (proj₁ ([F] ⊢Δ [σ′]))
             ⊢Fₜ′ = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F′) [liftσ′]))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′) [liftσ′]))
             ⊢F≡F′ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ)
                                     (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ′]′
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ′]))
             [ΠFG]′ = (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ′]
         in  Uₜ₌ (⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G)
                 (⟦ W ⟧ subst σ′ F ▹ subst (liftSubst σ′) G)
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G ∷ U)
                   (PE.sym (B-subst σ W F G))
                   (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ ▹ ⊢Gₜ)))
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ′ F ▹ subst (liftSubst σ′) G ∷ U)
                   (PE.sym (B-subst σ′ W F G))
                   (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ′ ▹ ⊢Gₜ′)))
                 ⟦ W ⟧-type ⟦ W ⟧-type (≅ₜ-W-cong W ⊢F ⊢F≡F′ ⊢G≡G′)
                 (proj₁ [ΠFG]) (proj₁ [ΠFG]′) (proj₂ [ΠFG] [σ′] [σ≡σ′]))

-- Validity of W-congruence as a term equality.
W-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E} W
           ([Γ] : ⊩ᵛ_ {n} Γ)
           ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
           ([H] : Γ ⊩ᵛ⟨ ¹ ⟩ H / [Γ])
           ([UF] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
           ([UH] : Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ])
           ([G]ₜ : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F]
                                / (λ {_} {Δ} {σ} → [UF] {Δ = Δ} {σ}))
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ U / [Γ] / Uᵛ [Γ])
           ([E]ₜ : Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ E ∷ U / [Γ] ∙ [H]
                                / (λ {_} {Δ} {σ} → [UH] {Δ = Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ U / [Γ] / Uᵛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ U / [Γ] ∙ [F]
                                  / (λ {_} {Δ} {σ} → [UF] {Δ = Δ} {σ}))
         → Γ ⊩ᵛ⟨ ¹ ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E ∷ U / [Γ] / Uᵛ [Γ]
W-congᵗᵛ {F = F} {G} {H} {E} W
         [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      ⊢H = escape (proj₁ ([H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univᵛ {A = G} {l′ = ⁰} (_∙_ {A = F} [Γ] [F])
                    (λ {_} {Δ} {σ} → [UF] {Δ = Δ} {σ}) [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F])
                           (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univᵛ {A = H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univᵛ {A = E} {l′ = ⁰} (_∙_ {A = H} [Γ] [H])
                                  (λ {_} {Δ} {σ} → [UH] {Δ = Δ} {σ}) [E]ₜ)
      [F≡H]ᵤ = univEqᵛ {A = F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F])
                               (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqᵛ {A = G} {E} (_∙_ {A = F} [Γ] [F])
                          (λ {_} {Δ} {σ} → [UF] {Δ = Δ} {σ}) [G]ᵤ₁ [G≡E]ₜ)
      ΠFGₜ = ⟦ W ⟧ⱼᵤ escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ]))
             ▹  escapeTerm (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                           (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
      ΠHEₜ = ⟦ W ⟧ⱼᵤ escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ]))
             ▹  escapeTerm (proj₁ ([UH] (⊢Δ ∙ ⊢H) [liftHσ]))
                           (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ]))
  in  Uₜ₌ (⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G)
          (⟦ W ⟧ subst σ H ▹ subst (liftSubst σ) E)
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ F ▹ subst (liftSubst σ) G ∷ U)
            (PE.sym (B-subst σ W F G))
            (idRedTerm:*: ΠFGₜ))
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ subst σ H ▹ subst (liftSubst σ) E ∷ U)
            (PE.sym (B-subst σ W H E))
            (idRedTerm:*: ΠHEₜ))
          ⟦ W ⟧-type ⟦ W ⟧-type
          (≅ₜ-W-cong W ⊢F (escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                        (escapeTermEq (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ])))
          (proj₁ (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ]))
          (proj₁ (⟦ W ⟧ᵛ {F = H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ]))
          (W-congᵛ {F = F} {G} {H} {E} W [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ])

-- Validity of non-dependent binding types.
ndᵛ : ∀ {F G l} W
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G / [Γ]
    → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ wk1 G / [Γ]
ndᵛ {F = F} {G} W [Γ] [F] [G] =
  ⟦ W ⟧ᵛ {F = F} {wk1 G} [Γ] [F] (wk1ᵛ {A = G} {F} [Γ] [F] [G])

-- Validity of non-dependent binding type congruence.
nd-congᵛ : ∀ {F F′ G G′ l} W
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] / [G])
         → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ wk1 G ≡ ⟦ W ⟧ F′ ▹ wk1 G′ / [Γ] / ndᵛ {F = F} {G} W [Γ] [F] [G]
nd-congᵛ {F = F} {F′} {G} {G′} W [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] =
  W-congᵛ {F = F} {wk1 G} {F′} {wk1 G′} W
          [Γ] [F] (wk1ᵛ {A = G} {F} [Γ] [F] [G])
          [F′] (wk1ᵛ {A = G′} {F′} [Γ] [F′] [G′])
          [F≡F′] (wk1Eqᵛ {A = G} {G′} {F} [Γ] [F] [G] [G≡G′])

-- Respecialized declarations at Π and Σ
Πᵛ : ∀ {Γ : Con Term n} {F G l} → _
Πᵛ {Γ = Γ} {F} {G} {l} = ⟦ BΠ ⟧ᵛ {Γ = Γ} {F} {G} {l}

Π-congᵛ : ∀ {Γ : Con Term n} {F G H E l} → _
Π-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} = W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} BΠ

Πᵗᵛ : ∀ {Γ : Con Term n} {F G} → _
Πᵗᵛ {Γ = Γ} {F} {G} = Wᵗᵛ {Γ = Γ} {F} {G} BΠ

Π-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E} → _
Π-congᵗᵛ  {Γ = Γ} {F} {G} {H} {E} = W-congᵗᵛ {Γ = Γ} {F} {G} {H} {E} BΠ

▹▹ᵛ : ∀ {Γ : Con Term n} {F G l} → _
▹▹ᵛ {Γ = Γ} {F} {G} {l} = ndᵛ {Γ = Γ} {F} {G} {l} BΠ

▹▹-congᵛ : ∀ {Γ : Con Term n} {F F′ G G′ l} → _
▹▹-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} = nd-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} BΠ

Σᵛ : ∀ {Γ : Con Term n} {F G l} → _
Σᵛ {Γ = Γ} {F} {G} {l} = ⟦ BΣ ⟧ᵛ {Γ = Γ} {F} {G} {l}

Σ-congᵛ : ∀ {Γ : Con Term n} {F G H E l} → _
Σ-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} = W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} BΣ

Σᵗᵛ : ∀ {Γ : Con Term n} {F G} → _
Σᵗᵛ {Γ = Γ} {F} {G} = Wᵗᵛ {Γ = Γ} {F} {G} BΣ

Σ-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E} → _
Σ-congᵗᵛ {Γ = Γ} {F} {G} {H} {E} = W-congᵗᵛ {Γ = Γ} {F} {G} {H} {E} BΣ

××ᵛ : ∀ {Γ : Con Term n} {F G l} → _
××ᵛ {Γ = Γ} {F} {G} {l} = ndᵛ {Γ = Γ} {F} {G} {l} BΣ

××-congᵛ : ∀ {Γ : Con Term n} {F F′ G G′ l} → _
××-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} = nd-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} BΣ
