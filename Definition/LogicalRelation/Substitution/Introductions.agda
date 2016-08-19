module Definition.LogicalRelation.Substitution.Introductions where

open import Definition.Untyped as U hiding (wk)
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
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


ℕₛ : ∀ {Γ l} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ]
ℕₛ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ _ x₂ → id (ℕ ⊢Δ)

Uₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
Uₛ [Γ] ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ _ x₂ → PE.refl

ℕₜₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ)
    → Γ ⊩ₛ⟨ ¹ ⟩t ℕ ∷ U / [Γ] / Uₛ [Γ]
ℕₜₛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕ ⊢Δ
                     [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                 in  (⊢ℕ , [ℕ]) , (λ _ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ])

univₛ : ∀ {A Γ l l'} ([Γ] : ⊩ₛ Γ)
        ([U] : Γ ⊩ₛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ l ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ l' ⟩ A / [Γ]
univₛ {l' = ⁰} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))
univₛ {A} {l' = ¹} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))

univEqₛ : ∀ {A B Γ l l'} ([Γ] : ⊩ₛ Γ)
          ([U] : Γ ⊩ₛ⟨ l' ⟩ U / [Γ])
          ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ₛ⟨ l' ⟩t' A ≡ B ∷ U / [Γ] / [U]
        → Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqₛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])

univₛ₁ : ∀ {A Γ} ([Γ] : ⊩ₛ Γ)
        ([U] : Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ ¹ ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
univₛ₁ [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))

zeroₛ : ∀ {Γ} ([Γ] : ⊩ₛ Γ)
      → Γ ⊩ₛ⟨ ¹ ⟩t zero ∷ ℕ / [Γ] / ℕₛ [Γ]
zeroₛ [Γ] ⊢Δ [σ] = ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ]
  , (λ _ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ])

sucₛ : ∀ {Γ n l} ([Γ] : ⊩ₛ Γ)
         ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
     → Γ ⊩ₛ⟨ l ⟩t n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ₛ⟨ l ⟩t suc n ∷ ℕ / [Γ] / [ℕ]
sucₛ ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
                          , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))

convₛ : ∀ {t A B Γ}
        ([Γ] : ⊩ₛ Γ)
        ([A]  : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
        ([B]  : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
      → Γ ⊩ₛ⟨ ¹ ⟩  A ≡ B / [Γ] / [A]
      → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
      → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ B / [Γ] / [B]
convₛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ'] [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ'] [σ≡σ'])

conv₂ₛ : ∀ {t A B Γ}
         ([Γ] : ⊩ₛ Γ)
         ([A]  : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
         ([B]  : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
       → Γ ⊩ₛ⟨ ¹ ⟩  A ≡ B / [Γ] / [A]
       → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ B / [Γ] / [B]
       → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
conv₂ₛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₂ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ'] [σ≡σ'] → convEqTerm₂ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ'] [σ≡σ'])

substS : ∀ {F G t Γ l} ([Γ] : ⊩ₛ Γ)
         ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
         ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
       → Γ ⊩ₛ⟨ l ⟩ G [ t ] / [Γ]
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

substSΠ₁ : ∀ {F G t Γ l l'}
           ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
           ([F] : Γ ⊩⟨ l' ⟩ F)
           ([t] : Γ ⊩⟨ l' ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]
substSΠ₁ (ℕ D) [F] [t] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
substSΠ₁ (ne D neK) [F] [t] = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
substSΠ₁ {F} {G} {t} (Π D ⊢F ⊢G [F] [G] G-ext) [F]₁ [t] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      Feq = PE.trans F≡F' (PE.sym (wk-id _ 0))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      ⊢Γ = wf (soundness [F]₁)
      [t]' = irrelevanceTerm' Feq [F]₁ ([F] T.base ⊢Γ) [t]
  in  PE.subst (λ x → _ ⊩⟨ _ ⟩ x) Geq ([G] T.base ⊢Γ [t]')
substSΠ₁ (emb {l< = 0<1} x) [F] [t] = emb {l< = 0<1} (substSΠ₁ x [F] [t])

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
substSΠ₂ (ℕ D) [ΠFG≡ΠF'G'] [F] [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']] =
  ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
substSΠ₂ (ne D neK) [ΠFG≡ΠF'G'] [F] [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']] =
  ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
substSΠ₂ (Π D ⊢F ⊢G [F] [G] G-ext) Π¹[ F'' , G'' , D' , A≡B , [F≡F'] , [G≡G'] ]
         [F]₁ [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      F'≡F'' , G'≡G'' = Π-PE-injectivity (whnfRed*' D' Π)
      Feq = PE.trans F≡F' (PE.sym (wk-id _ 0))
      F'eq = PE.trans F'≡F'' (PE.sym (wk-id _ 0))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      Geq' = PE.cong (λ x → x [ _ ]) (PE.trans G'≡G'' (PE.sym (wk-id _ 1)))
      ⊢Γ = wf (soundness [F]₁)
      [t]' = irrelevanceTerm' Feq [F]₁ ([F] T.base ⊢Γ) [t]
      [t']' = convTerm₂' F'eq ([F] T.base ⊢Γ) [F'] ([F≡F'] T.base ⊢Γ) [t']
      [t≡t']' = irrelevanceEqTerm' Feq [F]₁ ([F] T.base ⊢Γ) [t≡t']
      [Gt≡Gt'] = G-ext T.base ⊢Γ [t]' [t']' [t≡t']'
      [Gt'≡G't'] = [G≡G'] T.base ⊢Γ [t']'
  in  irrelevanceEq' Geq ([G] T.base ⊢Γ [t]') [G[t]]
        (transEq' PE.refl Geq' ([G] T.base ⊢Γ [t]') ([G] T.base ⊢Γ [t']')
                  [G'[t']] [Gt≡Gt'] [Gt'≡G't'])
substSΠ₂ (emb {l< = 0<1} x) [ΠFG≡ΠF'G'] [F] [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']] =
  substSΠ₂ x [ΠFG≡ΠF'G'] [F] [F'] [t] [t'] [t≡t'] [G[t]] [G'[t']]

substSΠ : ∀ {F G t Γ l}
          ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([ΠFG] : Γ ⊩ₛ⟨ l ⟩ Π F ▹ G / [Γ])
          ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ F / [Γ] / [F])
        → Γ ⊩ₛ⟨ l ⟩ G [ t ] / [Γ]
substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ] =
  let [σG[t]] = substSΠ₁ (proj₁ ([ΠFG] ⊢Δ [σ])) (proj₁ ([F] ⊢Δ [σ]))
                         (proj₁ ([t] ⊢Δ [σ]))
      [σG[t]]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLift G t))
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
          → Γ ⊩ₛ⟨ l ⟩ G [ t ] ≡ G [ u ] / [Γ] / substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t]
substSΠEq {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] [t≡u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , ⊢F' , ⊢G' , [F]' , [G]' , G-ext' = Π-elim [σΠFG]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σt]' = irrelevanceTerm' (PE.sym (wk-id (subst σ F) 0)) [σF] ([F]' T.base ⊢Δ) [σt]
      [σu]' = irrelevanceTerm' (PE.sym (wk-id (subst σ F) 0)) [σF] ([F]' T.base ⊢Δ) [σu]
      [σt≡σu] = [t≡u] ⊢Δ [σ]
      [G[t]] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.cong (λ x → x [ subst σ t ]) (wk-id (subst (liftSubst σ) G) 1)) ([G]' T.base ⊢Δ [σt]')
      [G[u]] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.cong (λ x → x [ subst σ u ]) (wk-id (subst (liftSubst σ) G) 1)) ([G]' T.base ⊢Δ [σu]')
  in  irrelevanceEq'' (PE.sym (singleSubstLift G t)) (PE.sym (singleSubstLift G u)) [G[t]] (proj₁ (substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ])) (substSΠ₂ [σΠFG] (reflEq [σΠFG]) [σF] [σF] [σt] [σu] [σt≡σu] [G[t]] [G[u]])

-- subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--           ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
--           ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
--           ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
--         → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
-- subst↑S [Γ] [F] [G] [t] ⊢Δ [σ] = ?

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
               (λ [tailσ] → Δ₁ ⊩⟨ l ⟩ head σ' ∷ subst (tail σ') F / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
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
      [G]a' a ρ ⊢Δ₁ [a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (G-substWkLemma a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in Π (idRed:*: ⊢ΠF▹G) (⊢F [σ]) (⊢G [σ]) (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
       (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
         let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                               (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
         in  [G]a' a ρ ⊢Δ₁ [a]')
      (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [b] [a≡b] →
         let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                               (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
             [b]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                               (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [b]
             [a≡b]' = irrelevanceEqTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                   (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a≡b]
         in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                             (PE.sym (G-substWkLemma b σ G))
                             (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                             ([G]a' a ρ ⊢Δ₁ [a]')
                             (proj₂ ([G]a a ρ ⊢Δ₁ [a]')
                                    (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ] , [b]') (reflSubst [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) , [a≡b]')))
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
             , Π-cong (⊢F [σ]) (soundnessEq (proj₁ ([F] ⊢Δ [σ])) (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']))
                      (soundnessEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                        ([wk1σ'] , neuTerm [F][wk1σ'] (var zero) (conv var0
                          (soundnessEq [F][wk1σ] (proj₂ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ]) [wk1σ'] [wk1σ≡wk1σ']))))
                        ([wk1σ≡wk1σ'] , neuEqTerm [F][wk1σ]
                          (var zero) (var zero) (var0 , var0 , refl var0))))
             , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']))
             , (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                      [ρσ'] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ']
                      [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      [a]'' = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ])) (proj₁ ([F] ⊢Δ₁ [ρσ'])) (proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ'] (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ'])) [a]'
                      [ρσa≡ρσ'a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']) [F] [a]'
                  in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                                      (PE.sym (G-substWkLemma a σ' G))
                                      (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                                      ([G]a' a ρ ⊢Δ₁ [a]')
                                      (proj₂ ([G]a a ρ ⊢Δ₁ [a]') (consSubstS {t = a} {A = F} [Γ]  ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ']) [F] [a]'') [ρσa≡ρσ'a]))
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
      _ , ⊢F' , ⊢G' , [F]' , [G]' , G-ext' = Π-elim [σΠFG]
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
                     in  irrelevanceEq'' (PE.sym (wk-subst F)) (PE.sym (wk-subst H)) (proj₁ ([F] ⊢Δ₁ [ρσ])) ([F]' ρ ⊢Δ₁) ([F≡H] ⊢Δ₁ [ρσ]))
        , (λ {Δ} {a} ρ ⊢Δ₁ [a] →
             let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                 [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                 [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'
             in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G)) (PE.sym (G-substWkLemma a σ E)) (proj₁ ([G] ⊢Δ₁ [aρσ])) ([G]' ρ ⊢Δ₁ [a]) ([G≡E] ⊢Δ₁ [aρσ])) ]

Πₜₛ : ∀ {F G Γ} ([Γ] : ⊩ₛ Γ)
      ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
      ([U] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
    → Γ ⊩ₛ⟨ ¹ ⟩t F ∷ U / [Γ] / Uₛ [Γ]
    → Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F] / (λ {Δ} {σ} → [U] {Δ} {σ})
    → Γ ⊩ₛ⟨ ¹ ⟩t Π F ▹ G ∷ U / [Γ] / Uₛ [Γ]
Πₜₛ {F} {G} {Γ} [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      ⊢Fₜ = soundnessTerm (U {l< = 0<1} ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢Gₜ = soundnessTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      [F]₀ = univₛ {F} [Γ] (Uₛ [Γ]) [Fₜ]
      [Gₜ]' = S.irrelevanceTerm {A = U} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [U] {Δ} {σ})
                                (λ {Δ} {σ} → Uₛ (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ}) [Gₜ]
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
                           (conv (var (⊢Δ ∙ ⊢F) (PE.subst (λ x → zero ∷ x ∈ (Δ ∙ subst σ F))
                                      (wk-subst F) here))
                                 (soundnessEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                              (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ']
                                                     (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ']))))
             ⊢F' = soundness (proj₁ ([F] ⊢Δ [σ']))
             ⊢Fₜ' = soundnessTerm (U {l< = 0<1} ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ']))
             ⊢Gₜ' = soundnessTerm (proj₁ ([U] (⊢Δ ∙ ⊢F') [liftσ'])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F') [liftσ']))
             ⊢F≡F' = soundnessTermEq (U {l< = 0<1} ⊢Δ) (proj₂ ([Fₜ] ⊢Δ [σ]) [σ'] [σ≡σ'])
             ⊢G≡G' = soundnessTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ']' (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ']))
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
           ([G]ₜ : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F] / (λ {Δ} {σ} → [UF] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ₛ⟨ ¹ ⟩t H ∷ U / [Γ] / Uₛ [Γ])
           ([E]ₜ : Γ ∙ H ⊩ₛ⟨ ¹ ⟩t E ∷ U / [Γ] ∙ [H] / (λ {Δ} {σ} → [UH] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ₛ⟨ ¹ ⟩t' F ≡ H ∷ U / [Γ] / Uₛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t' G ≡ E ∷ U / [Γ] ∙ [F] / (λ {Δ} {σ} → [UF] {Δ} {σ}))
         → Γ ⊩ₛ⟨ ¹ ⟩t' Π F ▹ G ≡ Π H ▹ E ∷ U / [Γ] / Uₛ [Γ]
Π-congₜₛ {F} {G} {H} {E} [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ ⊢Δ [σ] =
  let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      ⊢H = soundness (proj₁ ([H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univₛ {F} [Γ] (Uₛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univₛ {G} {l' = ⁰} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univₛ {H} [Γ] (Uₛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univₛ {E} {l' = ⁰} (_∙_ {A = H} [Γ] [H])
                                  (λ {Δ} {σ} → [UH] {Δ} {σ}) [E]ₜ)
      [F≡H]ᵤ = univEqₛ {F} {H} [Γ] (Uₛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqₛ {G} {E} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ᵤ₁
                          [G≡E]ₜ)
  in  U[ Π soundnessTerm {l = ¹} (U {l< = 0<1} ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ]))
         ▹ soundnessTerm (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ])) (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
       , Π soundnessTerm {l = ¹} (U {l< = 0<1} ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ]))
         ▹ soundnessTerm (proj₁ ([UH] (⊢Δ ∙ ⊢H) [liftHσ])) (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ]))
       , Π-cong ⊢F (soundnessTermEq (U {l< = 0<1} ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                   (soundnessTermEq (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ])) ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
       , proj₁ (Πₛ {F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ])
       , proj₁ (Πₛ {H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ])
       , Π-congₛ {F} {G} {H} {E} [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ] ]

appTerm : ∀ {F G t u Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm [F] [G[u]] (ℕ D) [t] [u] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
appTerm [F] [G[u]] (ne D neK) [t] [u] = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
appTerm [F] [G[u]] (Π D ⊢F ⊢G [F'] [G'] G-ext) (_ , _ , [t]) [u] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' (PE.trans F≡F' (PE.sym (wk-id _ 0))) [F] ([F'] T.base ⊢Γ) [u]
  in  irrelevanceTerm'' (PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G')))
                        (PE.cong (λ x → x ∘ _) (wk-id _ 0))
                        ([G'] T.base ⊢Γ [u]') [G[u]] ([t] T.base ⊢Γ [u]')
appTerm [F] [G[u]] (emb {l< = 0<1} x) [t] [u] = appTerm [F] [G[u]] x [t] [u]

app-congTerm : ∀ {F G t t' u u' Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t≡t'] : Γ ⊩⟨ l ⟩ t ≡ t' ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
          ([u'] : Γ ⊩⟨ l' ⟩ u' ∷ F / [F])
          ([u≡u'] : Γ ⊩⟨ l' ⟩ u ≡ u' ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ≡ t' ∘ u' ∷ G [ u ] / [G[u]]
app-congTerm [F] [G[u]] (ℕ D) [t≡t'] [u] [u'] [u≡u'] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
app-congTerm [F] [G[u]] (ne D neK) [t≡t'] [u] [u'] [u≡u'] = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
app-congTerm [F] [G[u]] (Π D ⊢F ⊢G [F]₁ [G] G-ext) (proj₁ , proj₂ , (proj₃ , proj₄ , proj₅) , proj₆) [u] [u'] [u≡u'] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      F≡wkidF' = PE.trans F≡F' (PE.sym (wk-id _ 0))
      t∘x≡wkidt∘x : {a b : Term} → U.wk id a Term.∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a 0)
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.base ⊢Γ) [u]
      [u']' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.base ⊢Γ) [u']
      [u≡u']' = irrelevanceEqTerm' F≡wkidF' [F] ([F]₁ T.base ⊢Γ) [u≡u']
      [tu≡t'u] = irrelevanceEqTerm'' t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                     ([G] T.base ⊢Γ [u]') [G[u]] (proj₆ T.base ⊢Γ [u]')
      [t'u≡t'u'] = irrelevanceEqTerm'' t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                       ([G] T.base ⊢Γ [u]') [G[u]] (proj₄ T.base ⊢Γ [u]' [u']' [u≡u']')
  in  transEqTerm [G[u]] [tu≡t'u] [t'u≡t'u']
app-congTerm [F] [G[u]] (emb {l< = 0<1} x) [t≡t'] [u] [u'] [u≡u'] = app-congTerm [F] [G[u]] x [t≡t'] [u] [u'] [u≡u']

appₛ : ∀ {F G t u Γ}
       ([Γ] : ⊩ₛ Γ)
       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
       ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
       ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ Π F ▹ G / [Γ] / [ΠFG])
       ([u] : Γ ⊩ₛ⟨ ¹ ⟩t u ∷ F / [Γ] / [F])
     → Γ ⊩ₛ⟨ ¹ ⟩t t ∘ u ∷ G [ u ] / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appₛ {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      proj₁[F] = proj₁ ([F] ⊢Δ [σ])
      proj₁[ΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      proj₁[t] = proj₁ ([t] ⊢Δ [σ])
      proj₁[u] = proj₁ ([u] ⊢Δ [σ])
      proj₁[G[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      proj₁[G[u]]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (singleSubstLift G u) proj₁[G[u]]
  in  irrelevanceTerm' (PE.sym (singleSubstLift G u)) proj₁[G[u]]' proj₁[G[u]] (appTerm proj₁[F] proj₁[G[u]]' proj₁[ΠFG] (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  ,   (λ [σ'] [σ≡σ'] →
         let proj₁[u'] = convTerm₂ proj₁[F] (proj₁ ([F] ⊢Δ [σ'])) (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']) (proj₁ ([u] ⊢Δ [σ']))
         in  irrelevanceEqTerm' (PE.sym (singleSubstLift G u)) proj₁[G[u]]' proj₁[G[u]] (app-congTerm proj₁[F] proj₁[G[u]]' proj₁[ΠFG] (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ']) (proj₁ ([u] ⊢Δ [σ])) proj₁[u'] (proj₂ ([u] ⊢Δ [σ]) [σ'] [σ≡σ'])))

app-congₛ : ∀ {F G t u a b Γ}
            ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
            ([t≡u] : Γ ⊩ₛ⟨ ¹ ⟩t' t ≡ u ∷ Π F ▹ G / [Γ] / [ΠFG])
            ([a] : Γ ⊩ₛ⟨ ¹ ⟩t a ∷ F / [Γ] / [F])
            ([b] : Γ ⊩ₛ⟨ ¹ ⟩t b ∷ F / [Γ] / [F])
            ([a≡b] : Γ ⊩ₛ⟨ ¹ ⟩t' a ≡ b ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ ¹ ⟩t' t ∘ a ≡ u ∘ b ∷ G [ a ] / [Γ] / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congₛ {F} {G} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (singleSubstLift G a) [G[a]]
  in  irrelevanceEqTerm' (PE.sym (singleSubstLift G a)) [G[a]]' [G[a]]
                         (app-congTerm (proj₁ ([F] ⊢Δ [σ])) [G[a]]' (proj₁ ([ΠFG] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]) (proj₁ ([a] ⊢Δ [σ])) (proj₁ ([b] ⊢Δ [σ])) ([a≡b] ⊢Δ [σ]))

lamₛ : ∀ {F G t Γ}
       ([Γ] : ⊩ₛ Γ)
       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩t t ∷ G / [Γ] ∙ [F] / [G])
     → Γ ⊩ₛ⟨ ¹ ⟩t lam t ∷ Π F ▹ G / [Γ] / Πₛ {F} {G} [Γ] [F] [G]
lamₛ {F} {G} {t} {Γ} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [ΠFG] = Πₛ {F} {G} [Γ] [F] [G]
      _ , ⊢F' , ⊢G' , [F]' , [G]' , G-ext  = Π-elim (proj₁ ([ΠFG] ⊢Δ [σ]))
      lamt : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ ¹ ⟩ subst σ (lam t) ∷ subst σ (Π F ▹ G) / proj₁ ([ΠFG] ⊢Δ [σ])
      lamt {Δ} {σ} ⊢Δ [σ] =
        let ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
            [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
            _ , ⊢F' , ⊢G' , [F]' , [G]' , G-ext  = Π-elim (proj₁ ([ΠFG] ⊢Δ [σ]))
        in  (lam ⊢F
            (soundnessTerm (proj₁ ([G] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))) (proj₁ ([t] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))))
        ,   (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [b] [a≡b] →
               let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                   [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                   [b]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                   [a≡b]' = irrelevanceEqTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
                   ⊢F₁' = soundness (proj₁ ([F] ⊢Δ₁ [ρσ]))
                   ⊢F₁ = soundness ([F]' ρ ⊢Δ₁)
                   [G]₁ = proj₁ ([G] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                     (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                   [G]₁' = irrelevanceΓ' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) [G]₁
                   [t]' = irrelevanceTermΓ'' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t)) [G]₁ [G]₁'
                                             (proj₁ ([t] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                                         (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                   ⊢a = soundnessTerm ([F]' ρ ⊢Δ₁) [a]
                   ⊢b = soundnessTerm ([F]' ρ ⊢Δ₁) [b]
                   ⊢t = soundnessTerm [G]₁' [t]'
                   G[a]' = proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                      ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                   G[a] = [G]' ρ ⊢Δ₁ [a]
                   t[a] = irrelevanceTerm'' (PE.sym (G-substWkLemma a σ G)) (PE.sym (G-substWkLemma a σ t)) G[a]' G[a]
                                            (proj₁ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                                        ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]')))
                   G[b]' = proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) b}
                                      ⊢Δ₁ (consSubstS {t = b} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [b]'))
                   G[b] = [G]' ρ ⊢Δ₁ [b]
                   t[b] = irrelevanceTerm'' (PE.sym (G-substWkLemma b σ G)) (PE.sym (G-substWkLemma b σ t)) G[b]' G[b]
                                            (proj₁ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) b}
                                                        ⊢Δ₁ (consSubstS {t = b} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [b]')))
                   lamt∘a≡t[a] = proj₂ (redSubstTerm (lam ⊢F₁ ⊢t ∘ ⊢a) (β-red ⊢F₁ ⊢t ⊢a) G[a] t[a])
                   G[a]≡G[b] = G-ext ρ ⊢Δ₁ [a] [b] [a≡b]
                   t[a]≡t[b] = irrelevanceEqTerm'' (PE.sym (G-substWkLemma a σ t)) (PE.sym (G-substWkLemma b σ t)) (PE.sym (G-substWkLemma a σ G)) G[a]' G[a] (proj₂ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁
                                   (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                              {σ' = consSubst (wkSubst (T.toWk ρ) σ) b}
                              (consSubstS {t = b} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [b]')
                              (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]'))
                   t[b]≡lamt∘b = convEqTerm₂ G[a] G[b] G[a]≡G[b] (symEqTerm G[b] (proj₂ (redSubstTerm (lam ⊢F₁ ⊢t ∘ ⊢b) (β-red ⊢F₁ ⊢t ⊢b) G[b] t[b])))
               in  transEqTerm G[a] lamt∘a≡t[a] (transEqTerm G[a] t[a]≡t[b] t[b]≡lamt∘b))
        ,   (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
               let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                   [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                   ⊢F₁' = soundness (proj₁ ([F] ⊢Δ₁ [ρσ]))
                   ⊢F₁ = soundness ([F]' ρ ⊢Δ₁)
                   [G]₁ = proj₁ ([G] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                     (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                   [G]₁' = irrelevanceΓ' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) [G]₁
                   [t]' = irrelevanceTermΓ'' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t)) [G]₁ [G]₁'
                                             (proj₁ ([t] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                                         (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                   ⊢a = soundnessTerm ([F]' ρ ⊢Δ₁) [a]
                   ⊢t = soundnessTerm [G]₁' [t]'
                   G[a]' = proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                      ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                   G[a] = [G]' ρ ⊢Δ₁ [a]
                   t[a] = irrelevanceTerm'' (PE.sym (G-substWkLemma a σ G)) (PE.sym (G-substWkLemma a σ t)) G[a]' G[a]
                                            (proj₁ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                                   ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]')))
               in  proj₁ (redSubstTerm (lam ⊢F₁ ⊢t ∘ ⊢a) (β-red ⊢F₁ ⊢t ⊢a) G[a] t[a])))
  in  lamt ⊢Δ [σ]
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         let [liftσ'] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ']
             _ , ⊢F'' , ⊢G'' , [F]'' , [G]'' , G-ext'  = Π-elim (proj₁ ([ΠFG] ⊢Δ [σ']))
             ⊢F' = soundness (proj₁ ([F] ⊢Δ [σ']))
             [G]₁ = proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ])
             [G]₁' = proj₁ ([G] (⊢Δ ∙ ⊢F') [liftσ'])
             [σΠFG≡σ'ΠFG] = proj₂ ([ΠFG] ⊢Δ [σ]) [σ'] [σ≡σ']
             ⊢t = soundnessTerm [G]₁ (proj₁ ([t] (⊢Δ ∙ ⊢F) [liftσ]))
             ⊢t' = soundnessTerm [G]₁' (proj₁ ([t] (⊢Δ ∙ ⊢F') [liftσ']))
             neuVar = neuTerm ([F]' (T.step T.base) (⊢Δ ∙ ⊢F)) (var 0) (var (⊢Δ ∙ ⊢F) here)
             σlamt∘a≡σ'lamt∘a : ∀ {Δ₁ a} → (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁) → ([a] : Δ₁ ⊩⟨ ¹ ⟩ a ∷ T.wkₜ ρ (subst σ F) / [F]' ρ ⊢Δ₁)
                 → Δ₁ ⊩⟨ ¹ ⟩ T.wkₜ ρ (subst σ (lam t)) ∘ a ≡ T.wkₜ ρ (subst σ' (lam t)) ∘ a ∷ T.wkLiftₜ ρ (subst (liftSubst σ) G) [ a ] / [G]' ρ ⊢Δ₁ [a]
             σlamt∘a≡σ'lamt∘a {Δ₁} {a} ρ ⊢Δ₁ [a] =
                let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    [ρσ'] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ']
                    [ρσ≡ρσ'] = wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']
                    ⊢F₁' = soundness (proj₁ ([F] ⊢Δ₁ [ρσ]))
                    ⊢F₁ = soundness ([F]' ρ ⊢Δ₁)
                    ⊢F₂' = soundness (proj₁ ([F] ⊢Δ₁ [ρσ']))
                    ⊢F₂ = soundness ([F]'' ρ ⊢Δ₁)
                    [σF≡σ'F] = proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ'] [ρσ≡ρσ']
                    [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                    [a]'' = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ])) (proj₁ ([F] ⊢Δ₁ [ρσ'])) [σF≡σ'F] [a]'
                    ⊢a = soundnessTerm ([F]' ρ ⊢Δ₁) [a]
                    ⊢a' = soundnessTerm ([F]'' ρ ⊢Δ₁) (irrelevanceTerm' (PE.sym (wk-subst F)) (proj₁ ([F] ⊢Δ₁ [ρσ'])) ([F]'' ρ ⊢Δ₁) [a]'')
                    G[a]' = proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                      ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                    G[a]₁' = proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ') a}
                                      ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ'] [F] [a]''))
                    G[a] = [G]' ρ ⊢Δ₁ [a]
                    G[a]'' = [G]'' ρ ⊢Δ₁ (irrelevanceTerm' (PE.sym (wk-subst F)) (proj₁ ([F] ⊢Δ₁ [ρσ'])) ([F]'' ρ ⊢Δ₁) [a]'')
                    [σG[a]≡σ'G[a]] = irrelevanceEq'' (PE.sym (G-substWkLemma a σ G)) (PE.sym (G-substWkLemma a σ' G)) G[a]' G[a]
                                       (proj₂ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁
                                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                                              {σ' = consSubst (wkSubst (T.toWk ρ) σ') a}
                                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ'] [F] [a]'')
                                              (consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ'] [F] [a]'))
                    [G]₁ = proj₁ ([G] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                      (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                    [G]₁' = irrelevanceΓ' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) [G]₁
                    [G]₂ = proj₁ ([G] {σ = liftSubst (wkSubst (T.toWk ρ) σ')}
                                      (⊢Δ₁ ∙ ⊢F₂') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ']))
                    [G]₂' = irrelevanceΓ' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) [G]₂
                    [t]' = irrelevanceTermΓ'' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t)) [G]₁ [G]₁'
                                             (proj₁ ([t] {σ = liftSubst (wkSubst (T.toWk ρ) σ)}
                                                         (⊢Δ₁ ∙ ⊢F₁') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                    [t]'' = irrelevanceTermΓ'' (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F))) (PE.sym (G-lamLemma G)) (PE.sym (G-lamLemma t)) [G]₂ [G]₂'
                                             (proj₁ ([t] {σ = liftSubst (wkSubst (T.toWk ρ) σ')}
                                                         (⊢Δ₁ ∙ ⊢F₂') (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ'])))
                    ⊢t = soundnessTerm [G]₁' [t]'
                    ⊢t' = soundnessTerm [G]₂' [t]''
                    t[a] = irrelevanceTerm'' (PE.sym (G-substWkLemma a σ G)) (PE.sym (G-substWkLemma a σ t)) G[a]' G[a]
                                            (proj₁ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                                   ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]')))
                    t[a]' = irrelevanceTerm'' (PE.sym (G-substWkLemma a σ' G)) (PE.sym (G-substWkLemma a σ' t)) G[a]₁' G[a]''
                                            (proj₁ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ') a}
                                                   ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ'] [F] [a]'')))
                    [σlamt∘a≡σt[a]] = proj₂ (redSubstTerm (lam ⊢F₁ ⊢t ∘ ⊢a) (β-red ⊢F₁ ⊢t ⊢a) G[a] t[a])
                    [σ't[a]≡σ'lamt∘a] = convEqTerm₂ G[a] G[a]'' [σG[a]≡σ'G[a]] (symEqTerm G[a]'' (proj₂ (redSubstTerm (lam ⊢F₂ ⊢t' ∘ ⊢a') (β-red ⊢F₂ ⊢t' ⊢a') G[a]'' t[a]')))
                    [σt[a]≡σ't[a]] = irrelevanceEqTerm'' (PE.sym (G-substWkLemma a σ t)) (PE.sym (G-substWkLemma a σ' t)) (PE.sym (G-substWkLemma a σ G)) G[a]' G[a]
                                       (proj₂ ([t] {σ = consSubst (wkSubst (T.toWk ρ) σ) a}
                                                  ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]'))
                                             {σ' = consSubst (wkSubst (T.toWk ρ) σ') a}
                                             (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ'] [F] [a]'')
                                             (consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ'] [F] [a]'))
                in  transEqTerm G[a] [σlamt∘a≡σt[a]] (transEqTerm G[a] [σt[a]≡σ't[a]] [σ't[a]≡σ'lamt∘a])
         in  fun-ext ⊢F (lam ⊢F ⊢t) (conv (lam ⊢F' ⊢t') (sym (soundnessEq (proj₁ ([ΠFG] ⊢Δ [σ])) [σΠFG≡σ'ΠFG])))
                     (soundnessTermEq (proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ]))
                                      (irrelevanceEqTerm' (idWkLiftSubstLemma σ G) ([G]' (T.step T.base) (⊢Δ ∙ ⊢F) neuVar) (proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ])) (σlamt∘a≡σ'lamt∘a (T.step T.base) (⊢Δ ∙ ⊢F) neuVar)))
         ,   lamt ⊢Δ [σ]
         ,   convTerm₂ (proj₁ ([ΠFG] ⊢Δ [σ])) (proj₁ ([ΠFG] ⊢Δ [σ'])) [σΠFG≡σ'ΠFG] (lamt ⊢Δ [σ'])
         ,   σlamt∘a≡σ'lamt∘a)

-- natrecTerm : ∀ {F Fn z s n Γ}
--              ([ℕ]  : Γ ⊩⟨ ¹ ⟩ ℕ)
--              ([F]  : Γ ∙ ℕ ⊩⟨ ¹ ⟩ F)
--              ([F₀] : Γ ⊩⟨ ¹ ⟩ F [ zero ])
--              ([F₊] : Γ ⊩⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑))
--              ([Fₙ] : Γ ⊩⟨ ¹ ⟩ Fn)
--            → Γ ⊩⟨ ¹ ⟩ z ∷ F [ zero ] / [F₀]
--            → Γ ⊩⟨ ¹ ⟩ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [F₊]
--            → ([n] : Γ ⊩⟨ ¹ ⟩ n ∷ ℕ / [ℕ])
--            → Γ ⊩⟨ ¹ ⟩ natrec F z s n ∷ Fn / [Fₙ]
-- natrecTerm [ℕ] [F] [F₀] [F₊] (U {l< = 0<1} ⊢Γ) [z] [s] [n] = {!!} , {!!}
-- natrecTerm [ℕ] [F] [F₀] [F₊] (ℕ D) [z] [s] [n] = {!!}
-- natrecTerm [ℕ] [F] [F₀] [F₊] (ne D neK) [z] [s] [n] = {!!}
-- natrecTerm [ℕ] [F] [F₀] [F₊] (Π D ⊢F ⊢G [F]₁ [G] G-ext) [z] [s] [n] = {!!}
-- natrecTerm [ℕ] [F] [F₀] [F₊] (emb x) [z] [s] [n] = {!!}

-- natrecₛ : ∀ {F z s n Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--           ([ℕ]  : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
--           ([F]  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F / [Γ] ∙ [ℕ])
--           ([F₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] / [Γ])
--           ([F₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
--           ([Fₙ] : Γ ⊩ₛ⟨ ¹ ⟩ F [ n ] / [Γ])
--         → Γ ⊩ₛ⟨ ¹ ⟩t z ∷ F [ zero ] / [Γ] / [F₀]
--         → Γ ⊩ₛ⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊]
--         → ([n] : Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ])
--         → Γ ⊩ₛ⟨ ¹ ⟩t natrec F z s n ∷ F [ n ] / [Γ] / [Fₙ]
-- natrecₛ {F} {z} {s} {n} [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n] {σ = σ} ⊢Δ [σ] =
--   natrecTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([F] (⊢Δ ∙ soundness (proj₁ ([ℕ] ⊢Δ [σ]))) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))) {!!} {!!} {!!} {!!} {!!} {!!} , {!!}

_⊩ₛ_⇒_∷_/_ : (Γ : Con Term) (t u A : Term) ([Γ] : ⊩ₛ Γ) → Set
Γ ⊩ₛ t ⇒ u ∷ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A

redSubstTermₛ : ∀ {A t u l Γ}
              → ([Γ] : ⊩ₛ Γ)
              → (∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ) → Δ ⊢ subst σ t ∷ subst σ A)
              → Γ ⊩ₛ t ⇒ u ∷ A / [Γ]
              → ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ₛ⟨ l ⟩t u ∷ A / [Γ] / [A]
              → Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
              × Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ A / [Γ] / [A]
redSubstTermₛ [Γ] ⊢t t⇒u [A] [u] =
  (λ ⊢Δ [σ] →
     let [σA] = proj₁ ([A] ⊢Δ [σ])
         [σt] , [σt≡σu] = redSubstTerm (⊢t ⊢Δ [σ]) (t⇒u ⊢Δ [σ]) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))
     in  [σt]
     ,   (λ [σ'] [σ≡σ'] →
            let [σ'A] = proj₁ ([A] ⊢Δ [σ'])
                [σA≡σ'A] = proj₂ ([A] ⊢Δ [σ]) [σ'] [σ≡σ']
                [σ't] , [σ't≡σ'u] = redSubstTerm (⊢t ⊢Δ [σ']) (t⇒u ⊢Δ [σ']) (proj₁ ([A] ⊢Δ [σ'])) (proj₁ ([u] ⊢Δ [σ']))
            in  transEqTerm [σA] [σt≡σu] (transEqTerm [σA] ((proj₂ ([u] ⊢Δ [σ])) [σ'] [σ≡σ']) (convEqTerm₂ [σA] [σ'A] [σA≡σ'A] (symEqTerm [σ'A] [σ't≡σ'u])))))
  , (λ ⊢Δ [σ] → proj₂ (redSubstTerm (⊢t ⊢Δ [σ]) (t⇒u ⊢Δ [σ]) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))))
