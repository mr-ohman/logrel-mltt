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


ℕₛ : ∀ {Γ l} ([Γ] : ⊩ₛ⟨ l ⟩ Γ) → Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ]
ℕₛ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ _ x₂ → id (ℕ ⊢Δ)

Uₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
Uₛ [Γ] ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ _ x₂ → PE.refl

ℕₜₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
    → Γ ⊩ₛ⟨ ¹ ⟩t ℕ ∷ U / [Γ] / Uₛ [Γ]
ℕₜₛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕ ⊢Δ
                     [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                 in  (⊢ℕ , [ℕ]) , (λ _ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ])

univₛ : ∀ {A Γ l} ([Γ] : ⊩ₛ⟨ l ⟩ Γ)
        ([Γ]₁ : ⊩ₛ⟨ ⁰ ⟩ Γ)
        ([U] : Γ ⊩ₛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ l ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ ⁰ ⟩ A / [Γ]₁
univₛ [Γ] [Γ]₁ [U] [A] ⊢Δ [σ] = let [σ]' = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                                    [A]₁ = univEq (proj₁ ([U] ⊢Δ [σ]')) (proj₁ ([A] ⊢Δ [σ]'))
                                in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ]')) [A]₁ ((proj₂ ([A] ⊢Δ [σ]')) (S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ x) (S.irrelevanceSubstEq [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ] [σ]' x₁)))

univₛ₁ : ∀ {A Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
        ([U] : Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ])
      → Γ ⊩ₛ⟨ ¹ ⟩t A ∷ U / [Γ] / [U]
      → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
univₛ₁ [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ x x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x x₁))

zeroₛ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
      → Γ ⊩ₛ⟨ ¹ ⟩t zero ∷ ℕ / [Γ] / ℕₛ [Γ]
zeroₛ [Γ] ⊢Δ [σ] = ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ]
  , (λ _ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ])

sucₛ : ∀ {Γ n l} ([Γ] : ⊩ₛ⟨ l ⟩ Γ)
         ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
     → Γ ⊩ₛ⟨ l ⟩t n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ₛ⟨ l ⟩t suc n ∷ ℕ / [Γ] / [ℕ]
sucₛ ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
                          , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))

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
          ([Γ] : ⊩ₛ⟨ l ⟩ Γ)
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

-- subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
--           ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
--           ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
--           ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
--         → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
-- subst↑S [Γ] [F] [G] [t] ⊢Δ [σ] = ?

Πₛ : ∀ {F G Γ l}
     ([Γ] : ⊩ₛ⟨ l ⟩ Γ)
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
               (Σ (Δ₁ ⊩ₛ⟨ l ⟩ tail σ' ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] → Δ₁ ⊩⟨ l ⟩ head σ' ∷ subst (tail σ') F / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ₛ⟨ l ⟩ consSubst (wkSubst (T.toWk ρ) σ) a ≡ σ' ∷ Γ ∙ F /
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

Πₜₛ : ∀ {F G Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
      ([Γ]₀ : ⊩ₛ⟨ ⁰ ⟩ Γ)
      ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
      ([U] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
    → Γ ⊩ₛ⟨ ¹ ⟩t F ∷ U / [Γ] / Uₛ [Γ]
    → Γ ∙ F ⊩ₛ⟨ ¹ ⟩t G ∷ U / [Γ] ∙ [F] / (λ {Δ} {σ} → [U] {Δ} {σ})
    → Γ ⊩ₛ⟨ ¹ ⟩t Π F ▹ G ∷ U / [Γ] / Uₛ [Γ]
Πₜₛ {F} {G} {Γ} [Γ] [Γ]₀ [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σ]' = S.irrelevanceSubst [Γ] [Γ]₀ ⊢Δ ⊢Δ [σ]
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = soundness (proj₁ ([F] ⊢Δ [σ]))
      ⊢Fₜ = soundnessTerm (U {l< = 0<1} ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢Gₜ = soundnessTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      [F]₀ = univₛ {F} [Γ] [Γ]₀ (Uₛ [Γ]) [Fₜ]
      [G]₀ = univₛ {G} (_∙_ {A = F} [Γ] [F]) ([Γ]₀ ∙ [F]₀) (λ {Δ} {σ} → [U] {Δ} {σ}) [Gₜ]
      [ΠFG] = (Πₛ {F} {G} [Γ]₀ [F]₀ [G]₀) ⊢Δ [σ]'
  in  (Π ⊢Fₜ ▹ ⊢Gₜ , proj₁ [ΠFG])
  ,   (λ [σ'] [σ≡σ'] →
         let [σ']' = S.irrelevanceSubst [Γ] [Γ]₀ ⊢Δ ⊢Δ [σ']
             [σ≡σ']' = S.irrelevanceSubstEq [Γ] [Γ]₀ ⊢Δ ⊢Δ [σ] [σ]' [σ≡σ']
             [liftσ'] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ']
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
             [ΠFG]' = (Πₛ {F} {G} [Γ]₀ [F]₀ [G]₀) ⊢Δ [σ']'
         in  U[ Π ⊢Fₜ ▹ ⊢Gₜ , Π ⊢Fₜ' ▹ ⊢Gₜ' , Π-cong ⊢F ⊢F≡F' ⊢G≡G'
             ,  proj₁ [ΠFG] , proj₁ [ΠFG]' , proj₂ [ΠFG] [σ']' [σ≡σ']' ])

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
       ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
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

-- lamTerm : ∀ {F G f Γ l l'}
--           ([F] : Γ ⊩⟨ l ⟩ F)
--           ([G] : Γ ∙ F ⊩⟨ l ⟩ G)
--           ([ΠFG] : Γ ⊩⟨ l' ⟩ Π F ▹ G)
--           ([f] : Γ ∙ F ⊩⟨ l ⟩ f ∷ G / [G])
--         → Γ ⊩⟨ l' ⟩ lam f ∷ Π F ▹ G / [ΠFG]
-- lamTerm [F] [G] (ℕ D) [f] = {!!}
-- lamTerm [F] [G] (ne D neK) [f] = {!!}
-- lamTerm [F] [G] (Π D ⊢F ⊢G [F]₁ [G]₁ G-ext) [f] =
--   let q = {!!}
--   in  lam (soundness [F]) (soundnessTerm [G] [f])
--   ,   (λ ρ ⊢Δ [a] [b] [a≡b] → {!!})
--   ,   (λ ρ ⊢Δ [a] → {!!})
-- lamTerm [F] [G] (emb {l< = 0<1} x) [f] = lamTerm [F] [G] x [f]

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
--   ,   (λ ρ ⊢Δ₁ [a] [b] [a≡b] → {!!})
--   ,   (λ ρ ⊢Δ₁ [a] → {!!}))
--   ,   (λ [σ'] [σ≡σ'] → {!!})
