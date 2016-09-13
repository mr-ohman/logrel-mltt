module Definition.LogicalRelation.Substitution.Introductions.Temp where

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
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE

open import Definition.LogicalRelation.Substitution.Introductions


lemma2 : ∀ {σ t G} → subst (consSubst (\ n → σ (suc n)) (subst (tail σ) t)) G
               PE.≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
lemma2 {t = t} {G = G} = PE.trans (substEq (\ { zero → PE.sym (subst-wk t) ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

lemma3 : ∀ {G t σ} →
         subst (consSubst (λ n → σ (suc n)) (subst σ t)) G PE.≡
         subst σ (subst (consSubst (λ x → var (suc x)) t) G)
lemma3 {G} {t} {σ} = PE.trans (substEq (\ { zero → PE.refl ; (suc x) → PE.refl }) G)  (PE.sym (substCompEq G))

subst↑S : ∀ {F G t Γ l} ([Γ] : ⊩ₛ Γ)
          ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ∙ F ⊩ₛ⟨ l ⟩t t ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ {F} {F} [Γ] [F] [F])
        → Γ ∙ F ⊩ₛ⟨ l ⟩ G [ t ]↑ / [Γ] ∙ [F]
subst↑S {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ₛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]' = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t] ⊢Δ [σ]))
      G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ
                               (proj₁ [σ] , [t]'))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G} {t} {σ}) G[t]
  in  G[t]'
  ,   (λ {σ'} [σ'] [σ≡σ'] →
         let [σ't] = irrelevanceTerm' (subst-wk F) (proj₁ ([wk1F] {σ = σ'} ⊢Δ [σ'])) (proj₁ ([F] {σ = tail σ'} ⊢Δ (proj₁ [σ']))) (proj₁ ([t] ⊢Δ [σ']))
             [σt≡σ't] = irrelevanceEqTerm' (subst-wk F) [σwk1F] [σwk1F]'
                                           (proj₂ ([t] ⊢Δ [σ]) {σ' = σ'} [σ'] [σ≡σ'])
             [σG[t]≡σ'G[t]] = proj₂ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ (proj₁ [σ] , [t]')) {σ' = consSubst (tail σ') (subst σ' t)} (proj₁ [σ'] , [σ't]) (proj₁ [σ≡σ'] , [σt≡σ't])
         in irrelevanceEq'' (lemma3 {G} {t} {σ}) (lemma3 {G} {t} {σ'}) G[t] G[t]' [σG[t]≡σ'G[t]])

subst↑SEq : ∀ {F G G' t t' Γ l} ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([G'] : Γ ∙ F ⊩ₛ⟨ l ⟩ G' / [Γ] ∙ [F])
            ([G≡G'] : Γ ∙ F ⊩ₛ⟨ l ⟩ G ≡ G' / [Γ] ∙ [F] / [G])
            ([t] : Γ ∙ F ⊩ₛ⟨ l ⟩t t ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ {F} {F} [Γ] [F] [F])
            ([t'] : Γ ∙ F ⊩ₛ⟨ l ⟩t t' ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ {F} {F} [Γ] [F] [F])
            ([t≡t'] : Γ ∙ F ⊩ₛ⟨ l ⟩t' t ≡ t' ∷ wk1 F / [Γ] ∙ [F] / wk1ₛ {F} {F} [Γ] [F] [F])
          → Γ ∙ F ⊩ₛ⟨ l ⟩ G [ t ]↑ ≡ G' [ t' ]↑ / [Γ] ∙ [F] / subst↑S {F} {G} {t} [Γ] [F] [G] [t]
subst↑SEq {F} {G} {G'} {t} {t'} [Γ] [F] [G] [G'] [G≡G'] [t] [t'] [t≡t'] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ₛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]' = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t] ⊢Δ [σ]))
      [t']' = irrelevanceTerm' (subst-wk F) [σwk1F] [σwk1F]' (proj₁ ([t'] ⊢Δ [σ]))
      [t≡t']' = irrelevanceEqTerm' (subst-wk F) [σwk1F] [σwk1F]' ([t≡t'] ⊢Δ [σ])
      G[t] = proj₁ ([G] ⊢Δ (proj₁ [σ] , [t]'))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G} {t} {σ}) G[t]
      G'[t] = proj₁ ([G'] ⊢Δ (proj₁ [σ] , [t]'))
      G'[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G'} {t} {σ}) G'[t]
      G'[t'] = proj₁ ([G'] ⊢Δ (proj₁ [σ] , [t']'))
      G'[t']' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (lemma3 {G'} {t'} {σ}) G'[t']
      G[t]≡G'[t] = irrelevanceEq'' (lemma3 {G} {t} {σ}) (lemma3 {G'} {t} {σ}) G[t] G[t]' ([G≡G'] ⊢Δ (proj₁ [σ] , [t]'))
      G'[t]≡G'[t'] = irrelevanceEq'' (lemma3 {G'} {t} {σ}) (lemma3 {G'} {t'} {σ}) G'[t] G'[t]' (proj₂ ([G'] ⊢Δ (proj₁ [σ] , [t]')) (proj₁ [σ] , [t']') (reflSubst [Γ] ⊢Δ (proj₁ [σ]) , [t≡t']'))
  in  transEq G[t]' G'[t]' G'[t']' G[t]≡G'[t] G'[t]≡G'[t']

lemma4 : ∀ ρ σ a x → substComp (liftSubst σ)
      (purge (lift ρ) (consSubst idSubst a)) x
      PE.≡ consSubst (wkSubst ρ σ) a x
lemma4 ρ σ a zero = PE.refl
lemma4 ρ σ a (suc x) = PE.trans (subst-wk (σ x)) (PE.sym (wk2subst ρ (σ x)))

fun-extₛ : ∀ {f g F G Γ l}
           ([Γ] : ⊩ₛ Γ)
           ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ₛ⟨ l ⟩ G / [Γ] ∙ [F])
         → let [ΠFG] = Πₛ {F} {G} [Γ] [F] [G] in
           Γ ⊩ₛ⟨ l ⟩t f ∷ Π F ▹ G / [Γ] / [ΠFG]
         → Γ ⊩ₛ⟨ l ⟩t g ∷ Π F ▹ G / [Γ] / [ΠFG]
         → Γ ∙ F ⊩ₛ⟨ l ⟩t' wk1 f ∘ var zero ≡ wk1 g ∘ var zero ∷ G / [Γ] ∙ [F] / [G]
         → Γ ⊩ₛ⟨ l ⟩t' f ≡ g ∷ Π F ▹ G / [Γ] / [ΠFG]
fun-extₛ {f} {g} {F} {G} [Γ] [F] [G] [f] [g] [f0≡g0] {Δ} {σ} ⊢Δ [σ] =
  let [ΠFG] = Πₛ {F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , ⊢F , ⊢G , [F]' , [G]' , G-ext = Π-elim [σΠFG]
      [σG] = proj₁ ([G] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σf = soundnessTerm [σΠFG] (proj₁ ([f] ⊢Δ [σ]))
      ⊢σg = soundnessTerm [σΠFG] (proj₁ ([g] ⊢Δ [σ]))
      σf0≡σg0 = soundnessTermEq [σG] ([f0≡g0] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      σf0≡σg0' = PE.subst₂ (λ x y → Δ ∙ subst σ F ⊢ x ≡ y ∷ subst (liftSubst σ) G)
                           (PE.cong₂ _∘_ (PE.trans (subst-wk f) (PE.sym (wk-subst f))) PE.refl)
                           (PE.cong₂ _∘_ (PE.trans (subst-wk g) (PE.sym (wk-subst g))) PE.refl)
                           σf0≡σg0
  in  fun-ext ⊢F ⊢σf ⊢σg σf0≡σg0' , proj₁ ([f] ⊢Δ [σ]) , proj₁ ([g] ⊢Δ [σ])
  ,   (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
         let [a]' = irrelevanceTerm' (wk-subst F) ([F]' ρ ⊢Δ₁) (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
             fEq = PE.cong₂ _∘_ (PE.trans (subst-wk f) (PE.sym (wk-subst f))) PE.refl
             gEq = PE.cong₂ _∘_ (PE.trans (subst-wk g) (PE.sym (wk-subst g))) PE.refl
             GEq = PE.sym (PE.trans (subst-wk (subst (liftSubst σ) G)) (PE.trans (substCompEq G) (substEq (lemma4 (T.toWk ρ) σ a) G)))
         in  irrelevanceEqTerm'' fEq gEq GEq
                                 (proj₁ ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ] , [a]')))
                                 ([G]' ρ ⊢Δ₁ [a])
                                 ([f0≡g0] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ] , [a]')))

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
         → Γ ⊩ₛ⟨ l ⟩ G [ t ] ≡ G' [ t' ] / [Γ] / substS {F} {G} {t} [Γ] [F] [G] [t]
substSEq {F} {F'} {G} {G'} {t} {t'} [Γ] [F] [F'] [F≡F'] [G] [G'] [G≡G'] [t] [t'] [t≡t'] {σ = σ} ⊢Δ [σ] =
  let G[t] = (proj₁ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ
                    (consSubstS {t = subst σ t} {A = F} [Γ] ⊢Δ [σ] [F] (proj₁ ([t] ⊢Δ [σ])))))
      G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G))) G[t]
      [t]' = convₛ {t} {F} {F'} [Γ] [F] [F'] [F≡F'] [t]
      G'[t] = (proj₁ ([G'] {σ = consSubst σ (subst σ t)} ⊢Δ
                     (consSubstS {t = subst σ t} {A = F'} [Γ] ⊢Δ [σ] [F'] (proj₁ ([t]' ⊢Δ [σ])))))
      G[t]≡G'[t] = irrelevanceEq' (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G))) G[t] G[t]' ([G≡G'] {σ = consSubst σ (subst σ t)} ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G'[t]≡G'[t'] = irrelevanceEq'' PE.refl (PE.sym (PE.trans (substCompEq G') (substEq substConcatSingleton' G'))) G'[t] G'[t]
                       (proj₂ ([G'] {σ = consSubst σ (subst σ t)}
                                    ⊢Δ ([σ] , proj₁ ([t]' ⊢Δ [σ])))
                              {σ' = consSubst σ (subst σ t')}
                              ([σ] , proj₁ ([t'] ⊢Δ [σ]))
                              (reflSubst [Γ] ⊢Δ [σ] ,
                                convEqₛ {t} {t'} {F} {F'} [Γ] [F] [F'] [F≡F'] [t≡t'] ⊢Δ [σ]))
      G'[t'] = (proj₁ ([G'] {σ = consSubst σ (subst σ t')} ⊢Δ
                    (consSubstS {t = subst σ t'} {A = F'} [Γ] ⊢Δ [σ] [F'] (proj₁ ([t'] ⊢Δ [σ])))))
      G'[t']' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq G') (substEq substConcatSingleton' G'))) G'[t']
  in  transEq G[t]' G'[t] G'[t']' G[t]≡G'[t] G'[t]≡G'[t']

reflₛ : ∀ {A Γ l}
        ([Γ] : ⊩ₛ Γ)
        ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
      → Γ ⊩ₛ⟨ l ⟩ A ≡ A / [Γ] / [A]
reflₛ [Γ] [A] ⊢Δ [σ] =
  reflEq (proj₁ ([A] ⊢Δ [σ]))

reflₜₛ : ∀ {A t Γ l}
         ([Γ] : ⊩ₛ Γ)
         ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
         ([t] : Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A])
       → Γ ⊩ₛ⟨ l ⟩t' t ≡ t ∷ A / [Γ] / [A]
reflₜₛ [Γ] [A] [t] ⊢Δ [σ] =
  reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))

sucCase : ∀ {F Γ l} ([Γ] : ⊩ₛ Γ)
          ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
          ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
        → Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ]
sucCase {F} {Γ} {l} [Γ] [ℕ] [F] =
  Πₛ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} [Γ] [ℕ]
     (▹▹ₛ {F} {F [ suc (var zero) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]
         (subst↑S {ℕ} {F} {suc (var zero)} [Γ] [ℕ] [F]
           (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ})))

-- TODO add helper functions to reduce repetition
sucCaseCong : ∀ {F F' Γ l} ([Γ] : ⊩ₛ Γ)
              ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
              ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
              ([F'] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F' / [Γ] ∙ [ℕ])
              ([F≡F'] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F ≡ F' / [Γ] ∙ [ℕ] / [F])
        → Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                  ≡ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
                  / [Γ] / sucCase {F} [Γ] [ℕ] [F]
sucCaseCong {F} {F'} {Γ} {l} [Γ] [ℕ] [F] [F'] [F≡F'] =
  Π-congₛ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} {ℕ} {F' ▹▹ F' [ suc (var zero) ]↑} [Γ]
          [ℕ] (▹▹ₛ {F} {F [ suc (var zero) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]
         (subst↑S {ℕ} {F} {suc (var zero)} [Γ] [ℕ] [F]
           (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ})))
          [ℕ] (▹▹ₛ {F'} {F' [ suc (var zero) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F']
         (subst↑S {ℕ} {F'} {suc (var zero)} [Γ] [ℕ] [F']
           (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ})))
          (reflₛ {ℕ} [Γ] [ℕ]) (▹▹-congₛ {F} {F'} {F [ suc (var zero) ]↑} {F' [ suc (var zero) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F] [F'] [F≡F'] ((subst↑S {ℕ} {F} {suc (var zero)} [Γ] [ℕ] [F]
           (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ}))) ((subst↑S {ℕ} {F'} {suc (var zero)} [Γ] [ℕ] [F']
           (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ}))) (subst↑SEq {ℕ} {F} {F'} {suc (var zero)} {suc (var zero)} [Γ] [ℕ] [F] [F'] [F≡F'] (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ}) (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ})
             (λ {Δ} {σ} → reflₜₛ {ℕ} {suc (var zero)} (_∙_ {A = ℕ} [Γ] [ℕ]) (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ}) (λ {Δ} {σ} → sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
             (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
             (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ}) {Δ} {σ})))
