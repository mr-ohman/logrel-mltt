module Definition.LogicalRelation.Substitution.Introductions where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


ℕₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ]
ℕₛ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ _ x₂ → id (ℕ ⊢Δ)

Uₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
Uₛ [Γ] ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ _ x₂ → PE.refl

ℕₜₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
    → Γ ⊩ₛ⟨ ¹ ⟩t ℕ ∷ U / [Γ] / Uₛ [Γ]
ℕₜₛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕ ⊢Δ
                     [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                 in  (⊢ℕ , [ℕ]) , (λ _ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ])

univₛ : ∀ {A Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
        ([U] : Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ ¹ ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
univₛ [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ _ x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) {!!} x₁))

zeroₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
      → Γ ⊩ₛ⟨ ¹ ⟩t zero ∷ ℕ / [Γ] / ℕₛ [Γ]
zeroₛ [Γ] ⊢Δ [σ] = ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ]
  , (λ _ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ])

sucₛ : ∀ {Γ n} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
         ([ℕ] : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
     → Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ₛ⟨ ¹ ⟩t suc n ∷ ℕ / [Γ] / [ℕ]
sucₛ ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
                          , (λ _ x → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) {!!} x))

substS : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
         ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
         ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
       → Γ ⊩ₛ⟨ ¹ ⟩ G [ t ] / [Γ]
substS {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let G[t] = (proj₁ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ
                    (consSubstS {t = subst σ t} {A = F} [Γ] ⊢Δ [σ] [F] (proj₁ ([t] ⊢Δ [σ])))))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                      G[t]

  in  G[t]' , (λ {σ'} [σ'] [σ≡σ'] → irrelevanceEq'' (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                                          (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                                          G[t] G[t]' (proj₂ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ
                    (consSubstS {t = subst σ t} {A = F} [Γ] ⊢Δ [σ] [F] (proj₁ ([t] ⊢Δ [σ]))))
                    (consSubstS {t = subst σ' t} {A = F} [Γ] ⊢Δ [σ'] [F] (proj₁ ([t] ⊢Δ [σ']))) (([σ≡σ'] , (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ'])))))

postulate TODO : ∀ {a} {A : Set a} → A

Πₛ : ∀ {F G Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
               ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
             → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F]
             → Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ]
Πₛ {F} {G} {Γ} [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ'} [σ'] = [F] {σ = σ'} ⊢Δ [σ']
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ'} [σ'] = soundness (proj₁ ([F]σ {σ'} [σ']))
      [G]σ {σ'} [σ'] = [G] {σ = liftSubst σ'} (⊢Δ ∙ ⊢F [σ'])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ'])
      ⊢G {σ'} [σ'] = soundness (proj₁ ([G]σ {σ'} [σ']))
      ⊢ΠF▹G = Π ⊢F [σ] ▹ ⊢G [σ]
      [G]a : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ ¹ ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])))
           → Σ (Δ₁ ⊩⟨ ¹ ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G)
               (λ [Aσ] →
               {σ' : Nat → Term} →
               Δ₁ ⊩ₛ⟨ ¹ ⟩ consSubst (wkSubst (T.toWk ρ) σ) a ≡ σ' ∷ Γ ∙ F /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ ¹ ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G ≡
               subst σ' G / [Aσ])
      [G]a a ρ ⊢Δ₁ [a] = ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                          [F] [a]))
      [G]a' : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
            → Δ₁ ⊩⟨ ¹ ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                 / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))
            → Δ₁ ⊩⟨ ¹ ⟩ T.wkLiftₜ ρ (subst (liftSubst σ) G) [ a ]
      [G]a' a ρ ⊢Δ₁ [a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (G-substWkLemma a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in Π (idRed:*: ⊢ΠF▹G) (⊢F [σ]) (⊢G [σ]) (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
       (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
         let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                               (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
         in  [G]a' a ρ ⊢Δ₁ [a]')
      (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [a≡b] →
         let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                               (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
             [a≡b]' = irrelevanceEqTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                   (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a≡b]
         in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                             (PE.sym (G-substWkLemma b σ G))
                             (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                             ([G]a' a ρ ⊢Δ₁ [a]')
                             (proj₂ ([G]a a ρ ⊢Δ₁ [a]')
                                    (reflSubst [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) , [a≡b]')))
  ,  (λ {σ'} [σ≡σ'] →
         let [σ'] : Δ ⊩ₛ⟨ ¹ ⟩ σ' ∷ Γ / [Γ] / ⊢Δ
             [σ'] = TODO
             var0 = var (⊢Δ ∙ ⊢F [σ])
                        (PE.subst (λ x → zero ∷ x ∈ (Δ ∙ subst σ F))
                                  (wk-subst F) here)
         in  Π¹[ _ , _ , id (Π ⊢F [σ'] ▹ ⊢G [σ'])
             , Π-cong (⊢F [σ]) (soundnessEq (proj₁ ([F] ⊢Δ [σ])) (proj₂ ([F] ⊢Δ [σ]) [σ≡σ']))
                         (soundnessEq (proj₁ ([G]σ [σ]))
                                      (proj₂ ([G]σ [σ])
                                      (wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ']
                                        , neuEqTerm (proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) (wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ])))
                                                    (var zero) (var zero) (var0 , var0 , refl var0))))
             , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ≡σ']))
             , (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
                  let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
                      [ρσa≡ρσ'a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']) [F] [a]'
                  in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                                      (PE.sym (G-substWkLemma a σ' G))
                                      (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                                      ([G]a' a ρ ⊢Δ₁ [a]')
                                      (proj₂ ([G]a a ρ ⊢Δ₁ [a]') [ρσa≡ρσ'a]))
             ])

-- Πₜₛ : ∀ {F G Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
--       ([U] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
--     → Γ ⊩ₛ⟨ ¹ ⟩t F ∷ U / [Γ] / Uₛ [Γ]
--     → Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F] / [U]
--     → Γ ⊩ₛ⟨ ¹ ⟩t Π F ▹ G ∷ U / [Γ] / Uₛ [Γ]
-- Πₜₛ {F} {G} {Γ} [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] = {!!}

-- appTerm : ∀ {F G t u Γ}
--           ([F] : Γ ⊩⟨ ¹ ⟩ F)
--           ([G] : Γ ∙ F ⊩⟨ ¹ ⟩ G)
--           ([ΠFG] : Γ ⊩⟨ ¹ ⟩ Π F ▹ G)
--           ([G[u]] : Γ ⊩⟨ ¹ ⟩ G [ u ])
--           ([t] : Γ ⊩⟨ ¹ ⟩ t ∷ Π F ▹ G / [ΠFG])
--           ([u] : Γ ⊩⟨ ¹ ⟩ u ∷ F / [F])
--         → Γ ⊩⟨ ¹ ⟩ t ∘ u ∷ G [ u ] / [G[u]]
-- appTerm {G = G} {u = u} [F] [G] [ΠFG] [G[u]] [t] [u] with G [ u ]
-- appTerm [F] [G] [ΠFG] (U ⊢Γ) [t] [u] | .U = ({!soundnessTerm [ΠFG] [t]!} ∘ (soundnessTerm [F] [u])) , {!!}
-- appTerm [F] [G] [ΠFG] (ℕ D) [t] [u] | G[u] = ℕ[ {!!} , {!!} , {!!} , {!!} ]
-- appTerm [F] [G] [ΠFG] (ne D neK) [t] [u] | G[u] = {!!}
-- appTerm [F] [G] [ΠFG] (Π D ⊢F ⊢G [F]₁ [G]₁ G-ext) [t] [u] | G[u] = {!!}
-- appTerm [F] [G] [ΠFG] (emb x) [t] [u] | G[u] = {!!}

-- appₛ : ∀ {F G t u Γ}
--        ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--        ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
--        ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
--        ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ Π F ▹ G / [Γ] / Πₛ {F} {G} [Γ] [F] [G])
--        ([u] : Γ ⊩ₛ⟨ ¹ ⟩t u ∷ F / [Γ] / [F])
--      → Γ ⊩ₛ⟨ ¹ ⟩t t ∘ u ∷ G [ u ] / [Γ] / substS {F} {G} {u} [Γ] [F] [G] [u]
-- appₛ [Γ] [F] [G] [t] [u] ⊢Δ [σ] = {!!} , (λ x → {!!})

-- lamₛ : ∀ {F G t Γ}
--        ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--        ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
--        ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
--        ([t] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t t ∷ G / [Γ] ∙ [F] / [G])
--      → Γ ⊩ₛ⟨ ¹ ⟩t lam t ∷ Π F ▹ G / [Γ] / Πₛ {F} {G} [Γ] [F] [G]
-- lamₛ {F} [Γ] [F] [G] [t] ⊢Δ [σ] =
--   let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
--   in  (lam ⊢F
--            (soundnessTerm (proj₁ ([G] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))) (proj₁ ([t] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))))
--   ,   (λ ρ ⊢Δ₁ [a] [b] [a≡b] → {!!}))
--   ,   (λ x → {!!} , {!!})
