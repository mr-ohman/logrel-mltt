module Definition.LogicalRelation.Substitution.Introductions.Natrec where

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


natrec-subst* : ∀ {Γ C c g n n' l} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
              → Γ ⊢ g ∷ Π ℕ ▹ (C ▹▹ C [ suc (var zero) ]↑)
              → Γ ⊢ n ⇒* n' ∷ ℕ
              → ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
              → Γ ⊩⟨ l ⟩ n' ∷ ℕ / [ℕ]
              → (∀ {t t'} → Γ ⊩⟨ l ⟩ t  ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t' ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t ≡ t' ∷ ℕ / [ℕ]
                          → Γ ⊢ C [ t ] ≡ C [ t' ])
              → Γ ⊢ natrec C c g n ⇒* natrec C c g n' ∷ C [ n ]
natrec-subst* C c g (id x) [ℕ] [n'] prop = id (natrec C c g x)
natrec-subst* C c g (x ⇨ n⇒n') [ℕ] [n'] prop =
  let q , w = redSubst*Term n⇒n' [ℕ] [n']
      a , s = redSubstTerm x [ℕ] q
  in  natrec-subst C c g x ⇨ conv* (natrec-subst* C c g n⇒n' [ℕ] [n'] prop)
                   (prop q a (symEqTerm [ℕ] s))

natrecTerm' : ∀ {F z s n Γ Δ σ l}
              ([Γ]  : ⊩ₛ Γ)
              ([F]  : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕₛ [Γ]))
              ([F₀] : Γ ⊩ₛ⟨ l ⟩ F [ zero ] / [Γ])
              ([F₊] : Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
              ([z]  : Γ ⊩ₛ⟨ l ⟩t z ∷ F [ zero ] / [Γ] / [F₀])
              ([s]  : Γ ⊩ₛ⟨ l ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊])
              (⊢Δ   : ⊢ Δ)
              ([σ]  : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
              ([σn] : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕ (idRed:*: (ℕ ⊢Δ)))
            → Δ ⊩⟨ l ⟩ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n ∷ subst (liftSubst σ) F [ n ]
                / PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma n σ F)) (proj₁ ([F] ⊢Δ ([σ] , [σn]))) --proj₁ ([Fₙ] ⊢Δ [σ])
natrecTerm' {F} {z} {s} {n} {Γ} {Δ} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] ℕ[ .(suc m) , d , suc {m} , [m] ] =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = soundness (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = soundness (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero) (soundnessTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) {!!} (soundnessTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = soundnessTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ])) ℕ[ suc m , d , suc {m} , [m] ]
      ⊢m = soundnessTerm {l = l} [σℕ] [m]
      [σsm] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) [σℕ] ℕ[ suc m , idRedTerm:*: (suc ⊢m) , suc , [m] ]
      [σn] = ℕ[ suc m , d , suc {m} , [m] ]
      [σn]' , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₛₘ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma (suc m) σ F)) (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [Fₙ≡Fₛₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (singleSubstLemma (suc m) σ F)) [σFₙ]' [σFₙ]
                                (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsm]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsm]))
      [σFₘ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq F) (substEq substConcatSingleton F))) (proj₁ ([F] ⊢Δ ([σ] , [m])))
      [σFₛₘ]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym {!!}) (proj₁ ([F] {σ = consSubst σ (suc m)} ⊢Δ ([σ] , [σsm])))
      [σF₊ₘ] = substSΠ₁ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [m]
      natrecM = appTerm [σFₘ] [σFₛₘ]' [σF₊ₘ] (appTerm [σℕ] [σF₊ₘ] (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])) [m])
                        (natrecTerm' {F} {z} {s} {m} {σ = σ} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [m])
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsm]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (soundnessEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
                  ⇨∷* (conv* (natrec-suc ⊢m ⊢F ⊢z ⊢s
                  ⇨   id (soundnessTerm [σFₛₘ] natrecM)) (sym (soundnessEq [σFₙ] [Fₙ≡Fₛₘ])))
  in  proj₁ (redSubst*Term reduction [σFₙ] (convTerm₂ [σFₙ] [σFₛₘ] [Fₙ≡Fₛₘ] natrecM))
natrecTerm' {F} {s = s} {n = n} {Γ = Γ} {Δ = Δ} {σ = σ} {l = l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] ℕ[ .zero , d , zero , _ ] =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = soundness (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = soundness (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero) (soundnessTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) {!!} (soundnessTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = soundnessTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ])) ℕ[ zero , d , zero , _ ]
      [σ0] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ]))  ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , _ ]
      [σn]' , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σn] = ℕ[ zero , d , zero , _ ]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σF₀] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma zero σ F)) (proj₁ ([F] ⊢Δ ([σ] , [σ0])))
      [Fₙ≡F₀]' = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [Fₙ≡F₀]'' = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                  (PE.trans (substEq substConcatSingleton' F) (PE.sym (singleSubstLemma zero σ F)))
                                  [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [σz] = proj₁ ([z] ⊢Δ [σ])
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (soundnessEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z) (sym (soundnessEq [σFₙ] [Fₙ≡F₀]'')))
  in  proj₁ (redSubst*Term reduction [σFₙ] (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀] [σz]))
natrecTerm' {F} {s = s} {n = n} {Γ = Γ} {Δ = Δ} {σ = σ} {l = l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] ℕ[ m , d , ne neM , ⊢m ] =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σn] = ℕ[ m , d , ne neM , ⊢m ]
      ⊢ℕ = soundness (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = soundness (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero) (soundnessTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) {!!} (soundnessTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = soundnessTerm [σℕ] [σn]
      [σm] = neuTerm [σℕ] neM ⊢m
      [σn]' , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₘ] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma m σ F)) (proj₁ ([F] ⊢Δ ([σ] , [σm])))
      [Fₙ≡Fₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (singleSubstLemma m σ F)) [σFₙ]' [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn]))) ([σ] , [σm]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σm]))
      natrecM = neuTerm [σFₘ] (natrec neM) (natrec ⊢F ⊢z ⊢s ⊢m)
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σm]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (soundnessEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
  in  proj₁ (redSubst*Term reduction [σFₙ] (convTerm₂ [σFₙ] [σFₘ] [Fₙ≡Fₘ] natrecM))

natrecₛ : ∀ {F z s n Γ} ([Γ] : ⊩ₛ Γ)
          ([ℕ]  : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F / [Γ] ∙ [ℕ])
          ([F₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] / [Γ])
          ([F₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
          ([Fₙ] : Γ ⊩ₛ⟨ ¹ ⟩ F [ n ] / [Γ])
        → Γ ⊩ₛ⟨ ¹ ⟩t z ∷ F [ zero ] / [Γ] / [F₀]
        → Γ ⊩ₛ⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊]
        → ([n] : Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ])
        → Γ ⊩ₛ⟨ ¹ ⟩t natrec F z s n ∷ F [ n ] / [Γ] / [Fₙ]
natrecₛ {F} {z} {s} {n} [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n] {Δ = Δ} {σ = σ}  ⊢Δ [σ] =
  let
    [F]' = (S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ]) (_∙_ {l = ¹} [Γ] (ℕₛ [Γ])) [F])
    [σn]' = (irrelevanceTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ])) (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ])))
    n' = subst σ n
  in irrelevanceTerm' {!!} (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (singleSubstLemma n' σ F)) (proj₁ ([F]' ⊢Δ ([σ] , [σn]'))))
                        (proj₁ ([Fₙ] ⊢Δ [σ]))
                   (natrecTerm' {F} {z} {s} {n'} {σ = σ} [Γ]
                                [F]'
                                [F₀] [F₊] [z] [s] ⊢Δ [σ]
                                [σn]')
 ,
  (λ [σ'] [σ≡σ'] → {!!})
