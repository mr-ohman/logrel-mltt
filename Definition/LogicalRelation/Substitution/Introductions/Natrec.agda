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
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE


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

natrecSucCaseLemma : ∀ {σ} (x : Nat) →
      (substComp (liftSubst σ)
        (wkSubst (step id)
        (consSubst (wk1Subst idSubst) (suc (var zero))))) x
      PE.≡
      (substComp (consSubst (wk1Subst idSubst) (suc (var zero)))
        (purge (step id) (liftSubst (liftSubst σ)))) x
natrecSucCaseLemma zero = PE.refl
natrecSucCaseLemma {σ} (suc x) =
  PE.trans (subst-wk (σ x))
           (PE.sym (PE.trans (wkIndex-step (step id))
                             (wk2subst (step (step id)) (σ x))))

natrecSucCase : ∀ σ F → Term.Π ℕ ▹
      (Π subst (liftSubst σ) F ▹
       subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var zero) ]↑)))
      PE.≡
      Π ℕ ▹
      (subst (liftSubst σ) F ▹▹
       subst (liftSubst σ) F [ suc (var zero) ]↑)
natrecSucCase σ F =
  PE.cong₂ Π_▹_ PE.refl
    (PE.cong₂ Π_▹_ PE.refl
       (PE.trans (PE.trans (subst-wk (F [ suc (var zero) ]↑))
                           (substCompEq F))
                 (PE.sym (PE.trans (wk-subst (subst (liftSubst σ) F))
                                   (PE.trans (substCompEq F)
                                             (substEq natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ F z s m σ (x : Nat) →
     (substComp (consSubst (λ x → var (suc x)) (suc (var 0)))
       (purge (step id)
        (substComp (liftSubst (liftSubst σ))
         (substComp (liftSubst (consSubst idSubst m))
          (consSubst idSubst
           (natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)))))) x
           PE.≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma F z s m σ zero =
  PE.cong suc (PE.trans (subst-wk m) (substIdEq m))
natrecIrrelevantSubstLemma F z s m σ (suc x) =
  PE.trans (subst-wk (U.wk (step id) (σ x)))
           (PE.trans (subst-wk (σ x))
                     (substIdEq (σ x)))

natrecIrrelevantSubst : ∀ F z s m σ →
      subst (consSubst σ (suc m)) F PE.≡
      subst (liftSubst (consSubst idSubst m))
      (subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var zero) ]↑)))
      [ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m ]
natrecIrrelevantSubst F z s m σ =
  -- TODO Make nicer
  PE.sym (PE.trans (substCompEq (subst (liftSubst (liftSubst σ))
        (U.wk (step id)
         (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F))))
         (PE.trans (substCompEq (U.wk (step id)
        (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F)))
        (PE.trans
           (subst-wk (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F))
           (PE.trans (substCompEq F)
                     (substEq (natrecIrrelevantSubstLemma F z s m σ) F)))))

natrecIrrelevantSubstLemma' : ∀ F z s n (x : Nat) →
-- TODO Make nicer
      (substComp (consSubst (λ z₁ → var (suc z₁)) (suc (var zero)))
       (purge (step id)
        (substComp (liftSubst (consSubst idSubst n))
         (consSubst idSubst (natrec F z s n))))) x
      PE.≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma' F z s n zero =
  PE.cong suc (PE.trans (subst-wk n) (substIdEq n))
natrecIrrelevantSubstLemma' F z s n (suc x) = PE.refl

natrecIrrelevantSubst' : ∀ F z s n →
      subst (liftSubst (consSubst idSubst n))
      (wk1 (F [ suc (var zero) ]↑))
      [ natrec F z s n ]
      PE.≡
      F [ suc n ]
natrecIrrelevantSubst' F z s n =
  PE.trans (substCompEq (U.wk (step id)
                              (subst (consSubst (λ x → var (suc x))
                                                (suc (var zero)))
                                     F)))
           (PE.trans (subst-wk (subst (consSubst (λ x → var (suc x))
                                                 (suc (var zero)))
                                      F))
                     (PE.trans (substCompEq F)
                               (substEq (natrecIrrelevantSubstLemma' F z s n)
                                        F)))

sucCase₃ : ∀ {Γ l} ([Γ] : ⊩ₛ Γ)
           ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
         → Γ ∙ ℕ ⊩ₛ⟨ l ⟩t suc (var zero) ∷ ℕ / [Γ] ∙ [ℕ]
                 / (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
sucCase₃ {Γ} {l} [Γ] [ℕ] {Δ} {σ} =
  sucₛ {n = var zero} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
       (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
       (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ'] [σ≡σ'] → proj₂ [σ≡σ'])) {Δ} {σ}

sucCase₂ : ∀ {F Γ l} ([Γ] : ⊩ₛ Γ)
           ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
           ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
         → Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F [ suc (var zero) ]↑ / [Γ] ∙ [ℕ]
sucCase₂ {F} {Γ} {l} [Γ] [ℕ] [F] =
  subst↑S {ℕ} {F} {suc (var zero)} [Γ] [ℕ] [F]
          (λ {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ} {σ})

sucCase₁ : ∀ {F Γ l} ([Γ] : ⊩ₛ Γ)
           ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
           ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
         → Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F ▹▹ F [ suc (var zero) ]↑ / [Γ] ∙ [ℕ]
sucCase₁ {F} {Γ} {l} [Γ] [ℕ] [F] =
  ▹▹ₛ {F} {F [ suc (var zero) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]
      (sucCase₂ {F} [Γ] [ℕ] [F])

sucCase : ∀ {F Γ l} ([Γ] : ⊩ₛ Γ)
          ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
          ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
        → Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ]
sucCase {F} {Γ} {l} [Γ] [ℕ] [F] =
  Πₛ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} [Γ] [ℕ]
     (sucCase₁ {F} [Γ] [ℕ] [F])

sucCaseCong : ∀ {F F' Γ l} ([Γ] : ⊩ₛ Γ)
              ([ℕ] : Γ ⊩ₛ⟨ l ⟩ ℕ / [Γ])
              ([F] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
              ([F'] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F' / [Γ] ∙ [ℕ])
              ([F≡F'] : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F ≡ F' / [Γ] ∙ [ℕ] / [F])
        → Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F  ▹▹ F  [ suc (var zero) ]↑)
                  ≡ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
                  / [Γ] / sucCase {F} [Γ] [ℕ] [F]
sucCaseCong {F} {F'} {Γ} {l} [Γ] [ℕ] [F] [F'] [F≡F'] =
  Π-congₛ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} {ℕ} {F' ▹▹ F' [ suc (var zero) ]↑}
          [Γ] [ℕ] (sucCase₁ {F} [Γ] [ℕ] [F]) [ℕ] (sucCase₁ {F'} [Γ] [ℕ] [F'])
          (reflₛ {ℕ} [Γ] [ℕ])
          (▹▹-congₛ {F} {F'} {F [ suc (var zero) ]↑} {F' [ suc (var zero) ]↑}
             (_∙_ {A = ℕ} [Γ] [ℕ]) [F] [F'] [F≡F']
             (sucCase₂ {F} [Γ] [ℕ] [F]) (sucCase₂ {F'} [Γ] [ℕ] [F'])
             (subst↑SEq {ℕ} {F} {F'} {suc (var zero)} {suc (var zero)}
                        [Γ] [ℕ] [F] [F'] [F≡F']
                        (λ {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ} {σ})
                        (λ {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ} {σ})
                        (λ {Δ} {σ} →
                           reflₜₛ {ℕ} {suc (var zero)} (_∙_ {A = ℕ} [Γ] [ℕ])
                                  (λ {Δ} {σ} → wk1ₛ {ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ} {σ})
                                  (λ {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ} {σ})
                           {Δ} {σ})))

natrecTerm : ∀ {F z s n Γ Δ σ l}
             ([Γ]  : ⊩ₛ Γ)
             ([F]  : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕₛ [Γ]))
             ([F₀] : Γ ⊩ₛ⟨ l ⟩ F [ zero ] / [Γ])
             ([F₊] : Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
             ([z]  : Γ ⊩ₛ⟨ l ⟩t z ∷ F [ zero ] / [Γ] / [F₀])
             ([s]  : Γ ⊩ₛ⟨ l ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                       / [Γ] / [F₊])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕ (idRed:*: (ℕ ⊢Δ)))
           → Δ ⊩⟨ l ⟩ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n
               ∷ subst (liftSubst σ) F [ n ]
               / irrelevance' (PE.sym (singleSubstLemma n σ F))
                              (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrecTerm {F} {z} {s} {n} {Γ} {Δ} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .(suc m) d (suc {m}) [m]) =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = wellformed (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = wellformed (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = wellformedTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ]))
                          (ℕₜ (suc m) d (suc {m}) [m])
      ⊢m = wellformedTerm {l = l} [σℕ] [m]
      [σsm] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) [σℕ]
                              (ℕₜ (suc m) (idRedTerm:*: (suc ⊢m)) suc [m])
      [σn] = ℕₜ (suc m) d (suc {m}) [m]
      [σn]' , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₛₘ] = irrelevance' (PE.sym (singleSubstLemma (suc m) σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [Fₙ≡Fₛₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                 (PE.sym (singleSubstLemma (suc m) σ F))
                                 [σFₙ]' [σFₙ]
                                 (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsm]))
      [σFₘ] = irrelevance' (PE.sym (PE.trans (substCompEq F)
                                             (substEq substConcatSingleton F)))
                           (proj₁ ([F] ⊢Δ ([σ] , [m])))
      [σFₛₘ]' = irrelevance' (natrecIrrelevantSubst F z s m σ)
                             (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [σF₊ₘ] = substSΠ₁ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [m]
      natrecM = appTerm [σFₘ] [σFₛₘ]' [σF₊ₘ]
                        (appTerm [σℕ] [σF₊ₘ]
                                 (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [m])
                        (natrecTerm {F} {z} {s} {m} {σ = σ}
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [m])
      natrecM' = irrelevanceTerm' (PE.trans
                                    (PE.sym (natrecIrrelevantSubst F z s m σ))
                                    (PE.sym (singleSubstLemma (suc m) σ F)))
                                  [σFₛₘ]' [σFₛₘ] natrecM
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsm]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t']))))
                  ⇨∷* (conv* (natrec-suc ⊢m ⊢F ⊢z ⊢s
                              ⇨ id (wellformedTerm [σFₛₘ] natrecM'))
                             (sym (wellformedEq [σFₙ] [Fₙ≡Fₛₘ])))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₛₘ] [Fₙ≡Fₛₘ] natrecM'))
natrecTerm {F} {z} {s} {n} {Γ} {Δ} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .zero d zero _) =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = wellformed (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = wellformed (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = wellformedTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ]))
                          (ℕₜ zero d zero _)
      [σ0] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) [σℕ]
                             (ℕₜ zero (idRedTerm:*: (zero ⊢Δ)) zero _)
      [σn]' , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σn] = ℕₜ zero d zero _
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σF₀] = irrelevance' (PE.sym (singleSubstLemma zero σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σ0])))
      [Fₙ≡F₀]' = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0])
                       (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [Fₙ≡F₀]'' = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                  (PE.trans (substEq substConcatSingleton' F)
                                            (PE.sym (singleSubstLemma zero σ F)))
                                  [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [σz] = proj₁ ([z] ⊢Δ [σ])
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t']))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (wellformedEq [σFₙ] [Fₙ≡F₀]'')))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀] [σz]))
natrecTerm {F} {z} {s} {n} {Γ} {Δ} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ m d (ne neM) ⊢m) =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σn] = ℕₜ m d (ne neM) ⊢m
      ⊢ℕ = wellformed (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = wellformed (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = wellformedTerm [σℕ] [σn]
      [σm] = neuTerm [σℕ] neM ⊢m
      [σn]' , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₘ] = irrelevance' (PE.sym (singleSubstLemma m σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σm])))
      [Fₙ≡Fₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (singleSubstLemma m σ F)) [σFₙ]' [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn]))) ([σ] , [σm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σm]))
      natrecM = neuTerm [σFₘ] (natrec neM) (natrec ⊢F ⊢z ⊢s ⊢m)
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σm]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t']))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₘ] [Fₙ≡Fₘ] natrecM))


natrec-congTerm : ∀ {F F' z z' s s' n m Γ Δ σ σ' l}
                  ([Γ]      : ⊩ₛ Γ)
                  ([F]      : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕₛ [Γ]))
                  ([F']     : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F' / _∙_ {l = l} [Γ] (ℕₛ [Γ]))
                  ([F≡F']   : Γ ∙ ℕ ⊩ₛ⟨ l ⟩ F ≡ F' / _∙_ {l = l} [Γ] (ℕₛ [Γ])
                                    / [F])
                  ([F₀]     : Γ ⊩ₛ⟨ l ⟩ F [ zero ] / [Γ])
                  ([F'₀]    : Γ ⊩ₛ⟨ l ⟩ F' [ zero ] / [Γ])
                  ([F₀≡F'₀] : Γ ⊩ₛ⟨ l ⟩ F [ zero ] ≡ F' [ zero ] / [Γ] / [F₀])
                  ([F₊]     : Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                                / [Γ])
                  ([F'₊]    : Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
                                / [Γ])
                  ([F₊≡F₊'] : Γ ⊩ₛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                                ≡ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
                                / [Γ] / [F₊])
                  ([z]      : Γ ⊩ₛ⟨ l ⟩t z ∷ F [ zero ] / [Γ] / [F₀])
                  ([z']     : Γ ⊩ₛ⟨ l ⟩t z' ∷ F' [ zero ] / [Γ] / [F'₀])
                  ([z≡z']   : Γ ⊩ₛ⟨ l ⟩t' z ≡ z' ∷ F [ zero ] / [Γ] / [F₀])
                  ([s]      : Γ ⊩ₛ⟨ l ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                                / [Γ] / [F₊])
                  ([s']     : Γ ⊩ₛ⟨ l ⟩t s'
                                ∷ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
                                / [Γ] / [F'₊])
                  ([s≡s']   : Γ ⊩ₛ⟨ l ⟩t' s ≡ s'
                                ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                                / [Γ] / [F₊])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ₛ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ']     : Δ ⊩ₛ σ' ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ']   : Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕ (idRed:*: (ℕ ⊢Δ)))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ ℕ / ℕ (idRed:*: (ℕ ⊢Δ)))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ ℕ / ℕ (idRed:*: (ℕ ⊢Δ)))
                → Δ ⊩⟨ l ⟩ natrec (subst (liftSubst σ) F)
                                  (subst σ z) (subst σ s) n
                    ≡ natrec (subst (liftSubst σ') F')
                             (subst σ' z') (subst σ' s') m
                    ∷ subst (liftSubst σ) F [ n ]
                    / irrelevance' (PE.sym (singleSubstLemma n σ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrec-congTerm {F} {F'} {z} {z'} {s} {s'} {n} {m} {Γ} {Δ} {σ} {σ'} {l}
                [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ .(suc n') d (suc {n'}) [n'])
                (ℕₜ .(suc m') d' (suc {m'}) [m'])
                (ℕₜ₌ .(suc n'') .(suc m'') d₁ d₁'
                     t≡u (suc {n''} {m''} [n''≡m''])) =
  let n''≡n' = suc-PE-injectivity (whrDet* (redₜ d₁ , suc) (redₜ d , suc))
      m''≡m' = suc-PE-injectivity (whrDet* (redₜ d₁' , suc) (redₜ d' , suc))
      [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ'ℕ] = proj₁ ([ℕ] ⊢Δ [σ'])
      [n'≡m'] = irrelevanceEqTerm'' n''≡n' m''≡m' PE.refl [σℕ] [σℕ] [n''≡m'']
      [σn] = ℕₜ (suc n') d suc [n']
      [σ'm] = ℕₜ (suc m') d' suc [m']
      [σn≡σ'm] = ℕₜ₌ (suc n'') (suc m'') d₁ d₁' t≡u (suc [n''≡m''])
      ⊢ℕ = wellformed [σℕ]
      ⊢F = wellformed (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n = wellformedTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ])) [σn]
      ⊢n' = wellformedTerm {l = l} [σℕ] [n']
      ⊢ℕ' = wellformed [σ'ℕ]
      ⊢F' = wellformed (proj₁ ([F'] (⊢Δ ∙ ⊢ℕ')
                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ'])))
      ⊢z' = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F' zero)
                     (wellformedTerm (proj₁ ([F'₀] ⊢Δ [σ']))
                                    (proj₁ ([z'] ⊢Δ [σ'])))
      ⊢s' = PE.subst (λ x → Δ ⊢ subst σ' s' ∷ x) (natrecSucCase σ' F')
                     (wellformedTerm (proj₁ ([F'₊] ⊢Δ [σ']))
                                    (proj₁ ([s'] ⊢Δ [σ'])))
      ⊢m  = wellformedTerm {l = l} (ℕ ([ ⊢ℕ' , ⊢ℕ' , id ⊢ℕ' ])) [σ'm]
      ⊢m' = wellformedTerm {l = l} [σ'ℕ] [m']
      [σsn'] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) [σℕ]
                               (ℕₜ (suc n') (idRedTerm:*: (suc ⊢n')) suc [n'])
      [σn]' , [σn≡σsn'] = redSubst*Term (redₜ d) [σℕ] [σsn']
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₛₙ'] = irrelevance' (PE.sym (singleSubstLemma (suc n') σ F))
                             (proj₁ ([F] ⊢Δ ([σ] , [σsn'])))
      [Fₙ≡Fₛₙ'] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                  (PE.sym (singleSubstLemma (suc n') σ F))
                                  [σFₙ]' [σFₙ]
                                  (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn'])
                                         (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn']))
      [Fₙ≡Fₛₙ']' = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                   (natrecIrrelevantSubst F z s n' σ)
                                   [σFₙ]' [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn'])
                                          (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn']))
      [σFₙ'] = irrelevance' (PE.sym (PE.trans (substCompEq F)
                                              (substEq substConcatSingleton F)))
                            (proj₁ ([F] ⊢Δ ([σ] , [n'])))
      [σFₛₙ']' = irrelevance' (natrecIrrelevantSubst F z s n' σ)
                              (proj₁ ([F] ⊢Δ ([σ] , [σsn'])))
      [σF₊ₙ'] = substSΠ₁ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [n']
      [σ'sm'] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) [σ'ℕ]
                                (ℕₜ (suc m') (idRedTerm:*: (suc ⊢m')) suc [m'])
      [σ'm]' , [σ'm≡σ'sm'] = redSubst*Term (redₜ d') [σ'ℕ] [σ'sm']
      [σ'F'ₘ]' = proj₁ ([F'] ⊢Δ ([σ'] , [σ'm]))
      [σ'F'ₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F')) [σ'F'ₘ]'
      [σ'Fₘ]' = proj₁ ([F] ⊢Δ ([σ'] , [σ'm]))
      [σ'Fₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F)) [σ'Fₘ]'
      [σ'F'ₛₘ'] = irrelevance' (PE.sym (singleSubstLemma (suc m') σ' F'))
                               (proj₁ ([F'] ⊢Δ ([σ'] , [σ'sm'])))
      [F'ₘ≡F'ₛₘ'] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F'))
                                    (PE.sym (singleSubstLemma (suc m') σ' F'))
                                    [σ'F'ₘ]' [σ'F'ₘ]
                                    (proj₂ ([F'] ⊢Δ ([σ'] , [σ'm]))
                                           ([σ'] , [σ'sm'])
                                           (reflSubst [Γ] ⊢Δ [σ'] , [σ'm≡σ'sm']))
      [σ'Fₘ'] = irrelevance' (PE.sym (PE.trans (substCompEq F)
                                               (substEq substConcatSingleton F)))
                             (proj₁ ([F] ⊢Δ ([σ'] , [m'])))
      [σ'F'ₘ'] = irrelevance' (PE.sym (PE.trans (substCompEq F')
                                                (substEq substConcatSingleton F')))
                              (proj₁ ([F'] ⊢Δ ([σ'] , [m'])))
      [σ'F'ₛₘ']' = irrelevance' (natrecIrrelevantSubst F' z' s' m' σ')
                                (proj₁ ([F'] ⊢Δ ([σ'] , [σ'sm'])))
      [σ'F'₊ₘ'] = substSΠ₁ (proj₁ ([F'₊] ⊢Δ [σ'])) [σ'ℕ] [m']
      [σFₙ'≡σ'Fₘ'] = irrelevanceEq'' (PE.sym (singleSubstLemma n' σ F))
                                     (PE.sym (singleSubstLemma m' σ' F))
                                     (proj₁ ([F] ⊢Δ ([σ] , [n']))) [σFₙ']
                                     (proj₂ ([F] ⊢Δ ([σ] , [n']))
                                            ([σ'] , [m']) ([σ≡σ'] , [n'≡m']))
      [σ'Fₘ'≡σ'F'ₘ'] = irrelevanceEq'' (PE.sym (singleSubstLemma m' σ' F))
                                       (PE.sym (singleSubstLemma m' σ' F'))
                                       (proj₁ ([F] ⊢Δ ([σ'] , [m'])))
                                       [σ'Fₘ'] ([F≡F'] ⊢Δ ([σ'] , [m']))
      [σFₙ'≡σ'F'ₘ'] = transEq [σFₙ'] [σ'Fₘ'] [σ'F'ₘ'] [σFₙ'≡σ'Fₘ'] [σ'Fₘ'≡σ'F'ₘ']
      [σFₙ≡σ'Fₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                   (PE.sym (singleSubstLemma m σ' F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn]))) [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn]))
                                          ([σ'] , [σ'm]) ([σ≡σ'] , [σn≡σ'm]))
      [σ'Fₘ≡σ'F'ₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F))
                                     (PE.sym (singleSubstLemma m σ' F'))
                                     [σ'Fₘ]' [σ'Fₘ] ([F≡F'] ⊢Δ ([σ'] , [σ'm]))
      [σFₙ≡σ'F'ₘ] = transEq [σFₙ] [σ'Fₘ] [σ'F'ₘ] [σFₙ≡σ'Fₘ] [σ'Fₘ≡σ'F'ₘ]
      natrecN = appTerm [σFₙ'] [σFₛₙ']' [σF₊ₙ']
                        (appTerm [σℕ] [σF₊ₙ'] (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [n'])
                        (natrecTerm {F} {z} {s} {n'} {σ = σ}
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n'])
      natrecN' = irrelevanceTerm' (PE.trans (PE.sym (natrecIrrelevantSubst F z s n' σ))
                                            (PE.sym (singleSubstLemma (suc n') σ F)))
                                  [σFₛₙ']' [σFₛₙ'] natrecN
      natrecM = appTerm [σ'F'ₘ'] [σ'F'ₛₘ']' [σ'F'₊ₘ']
                        (appTerm [σ'ℕ] [σ'F'₊ₘ'] (proj₁ ([F'₊] ⊢Δ [σ']))
                                 (proj₁ ([s'] ⊢Δ [σ'])) [m'])
                        (natrecTerm {F'} {z'} {s'} {m'} {σ = σ'}
                                    [Γ] [F'] [F'₀] [F'₊] [z'] [s'] ⊢Δ [σ'] [m'])
      natrecM' = irrelevanceTerm' (PE.trans (PE.sym (natrecIrrelevantSubst F' z' s' m' σ'))
                                            (PE.sym (singleSubstLemma (suc m') σ' F')))
                                  [σ'F'ₛₘ']' [σ'F'ₛₘ'] natrecM
      [σs≡σ's] = proj₂ ([s] ⊢Δ [σ]) [σ'] [σ≡σ']
      [σ's≡σ's'] = convEqTerm₂ (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([F₊] ⊢Δ [σ']))
                               (proj₂ ([F₊] ⊢Δ [σ]) [σ'] [σ≡σ']) ([s≡s'] ⊢Δ [σ'])
      [σs≡σ's'] = transEqTerm (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ's] [σ's≡σ's']
      appEq = convEqTerm₂ [σFₙ] [σFₛₙ']' [Fₙ≡Fₛₙ']'
                (app-congTerm [σFₙ'] [σFₛₙ']' [σF₊ₙ']
                  (app-congTerm [σℕ] [σF₊ₙ'] (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ's']
                                [n'] [m'] [n'≡m'])
                  (natrecTerm {F} {z} {s} {n'} {σ = σ}
                              [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n'])
                  (convTerm₂ [σFₙ'] [σ'F'ₘ'] [σFₙ'≡σ'F'ₘ']
                             (natrecTerm {F'} {z'} {s'} {m'} {σ = σ'}
                                         [Γ] [F'] [F'₀] [F'₊] [z'] [s']
                                         ⊢Δ [σ'] [m']))
                  (natrec-congTerm {F} {F'} {z} {z'} {s} {s'} {n'} {m'} {σ = σ}
                                   [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀]
                                   [F₊] [F'₊] [F₊≡F'₊] [z] [z'] [z≡z']
                                   [s] [s'] [s≡s']
                                   ⊢Δ [σ] [σ'] [σ≡σ'] [n'] [m'] [n'≡m']))
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsn']
                     (λ {t} {t'} [t] [t'] [t≡t'] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstLemma t σ F))
                                  (PE.sym (singleSubstLemma t' σ F))
                                  (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t'])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
                   ⇨∷* (conv* (natrec-suc ⊢n' ⊢F ⊢z ⊢s
                   ⇨   id (wellformedTerm [σFₛₙ'] natrecN'))
                          (sym (wellformedEq [σFₙ] [Fₙ≡Fₛₙ'])))
      reduction₂ = natrec-subst* ⊢F' ⊢z' ⊢s' (redₜ d') [σ'ℕ] [σ'sm']
                     (λ {t} {t'} [t] [t'] [t≡t'] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstLemma t σ' F'))
                                  (PE.sym (singleSubstLemma t' σ' F'))
                                  (wellformedEq (proj₁ ([F'] ⊢Δ ([σ'] , [t])))
                                               (proj₂ ([F'] ⊢Δ ([σ'] , [t]))
                                                      ([σ'] , [t'])
                                                      (reflSubst [Γ] ⊢Δ [σ'] , [t≡t']))))
                   ⇨∷* (conv* (natrec-suc ⊢m' ⊢F' ⊢z' ⊢s'
                   ⇨   id (wellformedTerm [σ'F'ₛₘ'] natrecM'))
                          (sym (wellformedEq [σ'F'ₘ] [F'ₘ≡F'ₛₘ'])))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₛₙ']
                                            [Fₙ≡Fₛₙ'] natrecN'))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ'F'ₘ]
                                 (convTerm₂ [σ'F'ₘ] [σ'F'ₛₘ']
                                            [F'ₘ≡F'ₛₘ'] natrecM'))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] appEq
                               (convEqTerm₂ [σFₙ] [σ'F'ₘ] [σFₙ≡σ'F'ₘ]
                                            (symEqTerm [σ'F'ₘ] eq₂)))
natrec-congTerm {F} {F'} {z} {z'} {s} {s'} {n} {m} {Γ} {Δ} {σ} {σ'} {l}
                [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ .zero d zero prop) (ℕₜ .zero d₁ zero prop₁)
                (ℕₜ₌ .zero .zero d₂ d' t≡u zero) =
  let [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = wellformed (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = wellformed (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                 (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢F' = wellformed (proj₁ ([F'] {σ = liftSubst σ'} (⊢Δ ∙ ⊢ℕ)
                                   (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ'])))
      ⊢z' = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F' zero)
                     (wellformedTerm (proj₁ ([F'₀] ⊢Δ [σ'])) (proj₁ ([z'] ⊢Δ [σ'])))
      ⊢s' = PE.subst (λ x → Δ ⊢ subst σ' s' ∷ x) (natrecSucCase σ' F')
                     (wellformedTerm (proj₁ ([F'₊] ⊢Δ [σ'])) (proj₁ ([s'] ⊢Δ [σ'])))
      ⊢n = wellformedTerm {l = l} (ℕ ([ ⊢ℕ , ⊢ℕ , id ⊢ℕ ]))
                          (ℕₜ zero d zero _)
      [σ0] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ]))
                             (ℕₜ zero (idRedTerm:*: (zero ⊢Δ)) zero _)
      [σ'0] = irrelevanceTerm {l = l} (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ']))
                              (ℕₜ zero (idRedTerm:*: (zero ⊢Δ)) zero _)
      [σn]' , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σ'm]' , [σ'm≡σ'0] = redSubst*Term (redₜ d') (proj₁ ([ℕ] ⊢Δ [σ'])) [σ'0]
      [σn] = ℕₜ zero d zero _
      [σ'm] = ℕₜ zero d' zero _
      [σn≡σ'm] = ℕₜ₌ zero zero d₂ d' t≡u zero
      [σn≡σ'0] = transEqTerm [σℕ] [σn≡σ'm] [σ'm≡σ'0]
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σ'Fₘ]' = proj₁ ([F] ⊢Δ ([σ'] , [σ'm]))
      [σ'Fₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F)) [σ'Fₘ]'
      [σ'F'ₘ]' = proj₁ ([F'] ⊢Δ ([σ'] , [σ'm]))
      [σ'F'ₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F')) [σ'F'ₘ]'
      [σFₙ≡σ'Fₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                   (PE.sym (singleSubstLemma m σ' F))
                                   [σFₙ]' [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ'] , [σ'm])
                                          ([σ≡σ'] , [σn≡σ'm]))
      [σ'Fₘ≡σ'F'ₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F))
                                     (PE.sym (singleSubstLemma m σ' F'))
                                     [σ'Fₘ]' [σ'Fₘ] ([F≡F'] ⊢Δ ([σ'] , [σ'm]))
      [σFₙ≡σ'F'ₘ] = transEq [σFₙ] [σ'Fₘ] [σ'F'ₘ] [σFₙ≡σ'Fₘ] [σ'Fₘ≡σ'F'ₘ]
      [σF₀] = irrelevance' (PE.sym (singleSubstLemma zero σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σ0])))
      [σ'F₀] = irrelevance' (PE.sym (singleSubstLemma zero σ' F))
                            (proj₁ ([F] ⊢Δ ([σ'] , [σ'0])))
      [Fₙ≡F₀]' = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [σFₙ≡σ'F₀]' = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ'] , [σ'0]) ([σ≡σ'] , [σn≡σ'0])
      [σFₙ≡σ'F₀] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]' [σFₙ] [σFₙ≡σ'F₀]'
      [F'ₘ≡F'₀]' = proj₂ ([F'] ⊢Δ ([σ'] , [σ'm])) ([σ'] , [σ'0])
                         (reflSubst [Γ] ⊢Δ [σ'] , [σ'm≡σ'0])
      [F'ₘ≡F'₀] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F'))
                                  (PE.sym (substCompEq F'))
                                  [σ'F'ₘ]' [σ'F'ₘ] [F'ₘ≡F'₀]'
      [Fₙ≡F₀]'' = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                  (PE.trans (substEq substConcatSingleton' F)
                                            (PE.sym (singleSubstLemma zero σ F)))
                                  [σFₙ]' [σFₙ] [Fₙ≡F₀]'
      [F'ₘ≡F'₀]'' = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F'))
                                    (PE.trans (substEq substConcatSingleton' F')
                                              (PE.sym (singleSubstLemma zero σ' F')))
                                    [σ'F'ₘ]' [σ'F'ₘ] [F'ₘ≡F'₀]'
      [σz] = proj₁ ([z] ⊢Δ [σ])
      [σ'z'] = proj₁ ([z'] ⊢Δ [σ'])
      [σz≡σ'z] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀]
                             (proj₂ ([z] ⊢Δ [σ]) [σ'] [σ≡σ'])
      [σ'z≡σ'z'] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ'])) [σFₙ≡σ'F₀]
                               ([z≡z'] ⊢Δ [σ'])
      [σz≡σ'z'] = transEqTerm [σFₙ] [σz≡σ'z] [σ'z≡σ'z']
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ F))
                                 (PE.sym (singleSubstLemma t' σ F))
                                 (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (wellformedEq [σFₙ] [Fₙ≡F₀]'')))
      reduction₂ = natrec-subst* ⊢F' ⊢z' ⊢s' (redₜ d') (proj₁ ([ℕ] ⊢Δ [σ'])) [σ'0]
                    (λ {t} {t'} [t] [t'] [t≡t'] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstLemma t σ' F'))
                                 (PE.sym (singleSubstLemma t' σ' F'))
                                 (wellformedEq (proj₁ ([F'] ⊢Δ ([σ'] , [t])))
                                              (proj₂ ([F'] ⊢Δ ([σ'] , [t]))
                                                     ([σ'] , [t'])
                                                     (reflSubst [Γ] ⊢Δ [σ'] , [t≡t']))))
                  ⇨∷* (conv* (natrec-zero ⊢F' ⊢z' ⊢s' ⇨ id ⊢z')
                             (sym (wellformedEq [σ'F'ₘ] [F'ₘ≡F'₀]'')))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ]))
                                            [Fₙ≡F₀] [σz]))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ'F'ₘ]
                                 (convTerm₂ [σ'F'ₘ] (proj₁ ([F'₀] ⊢Δ [σ']))
                                            [F'ₘ≡F'₀] [σ'z']))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] [σz≡σ'z']
                               (convEqTerm₂ [σFₙ] [σ'F'ₘ] [σFₙ≡σ'F'ₘ]
                                            (symEqTerm [σ'F'ₘ] eq₂)))
natrec-congTerm {F} {F'} {z} {z'} {s} {s'} {n} {m} {Γ} {Δ} {σ} {σ'} {l}
                [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ n' d (ne neN') ⊢n') (ℕₜ m' d' (ne neM') ⊢m')
                (ℕₜ₌ n'' m'' d₁ d₁' t≡u (ne x₂ x₃ prop₂)) =
  let n''≡n' = whrDet* (redₜ d₁ , ne x₂) (redₜ d , ne neN')
      m''≡m' = whrDet* (redₜ d₁' , ne x₃) (redₜ d' , ne neM')
      [ℕ] = ℕₛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ'ℕ] = proj₁ ([ℕ] ⊢Δ [σ'])
      [σn] = ℕₜ n' d (ne neN') ⊢n'
      [σ'm] = ℕₜ m' d' (ne neM') ⊢m'
      [σn≡σ'm] = ℕₜ₌ n'' m'' d₁ d₁' t≡u (ne x₂ x₃ prop₂)
      ⊢ℕ = wellformed (proj₁ ([ℕ] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ'F] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ']))
      [σ'F'] = proj₁ ([F'] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ']))
      ⊢F = wellformed [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢F' = wellformed [σ'F']
      ⊢z' = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F' zero)
                     (wellformedTerm (proj₁ ([F'₀] ⊢Δ [σ'])) (proj₁ ([z'] ⊢Δ [σ'])))
      ⊢s' = PE.subst (λ x → Δ ⊢ subst σ' s' ∷ x) (natrecSucCase σ' F')
                     (wellformedTerm (proj₁ ([F'₊] ⊢Δ [σ'])) (proj₁ ([s'] ⊢Δ [σ'])))
      ⊢σF≡σ'F = wellformedEq [σF] (proj₂ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                           (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
                                      {σ' = liftSubst σ'}
                                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ'])
                                      (liftSubstSEq {F = ℕ} [Γ] ⊢Δ [ℕ] [σ] [σ≡σ']))
      ⊢σz≡σ'z = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (singleSubstLift F zero)
                         (wellformedTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                          (proj₂ ([z] ⊢Δ [σ]) [σ'] [σ≡σ']))
      ⊢σs≡σ's = PE.subst (λ x → Δ ⊢ subst σ s ≡ subst σ' s ∷ x)
                         (natrecSucCase σ F)
                         (wellformedTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                          (proj₂ ([s] ⊢Δ [σ]) [σ'] [σ≡σ']))
      ⊢σ'F≡⊢σ'F' = wellformedEq [σ'F] ([F≡F'] (⊢Δ ∙ ⊢ℕ)
                               (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ']))
      ⊢σ'z≡⊢σ'z' = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                            (singleSubstLift F zero)
                            (conv (wellformedTermEq (proj₁ ([F₀] ⊢Δ [σ']))
                                                   ([z≡z'] ⊢Δ [σ']))
                                  (sym (wellformedEq (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₂ ([F₀] ⊢Δ [σ]) [σ'] [σ≡σ']))))
      ⊢σ's≡⊢σ's' = PE.subst (λ x → Δ ⊢ subst σ' s ≡ subst σ' s' ∷ x)
                            (natrecSucCase σ F)
                            (conv (wellformedTermEq (proj₁ ([F₊] ⊢Δ [σ']))
                                                   ([s≡s'] ⊢Δ [σ']))
                                  (sym (wellformedEq (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₂ ([F₊] ⊢Δ [σ]) [σ'] [σ≡σ']))))
      ⊢F≡F' = trans ⊢σF≡σ'F ⊢σ'F≡⊢σ'F'
      ⊢z≡z' = trans ⊢σz≡σ'z ⊢σ'z≡⊢σ'z'
      ⊢s≡s' = trans ⊢σs≡σ's ⊢σ's≡⊢σ's'
      ⊢n = wellformedTerm [σℕ] [σn]
      [σn'] = neuTerm [σℕ] neN' ⊢n'
      [σn]' , [σn≡σn'] = redSubst*Term (redₜ d) [σℕ] [σn']
      [σFₙ]' = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance' (PE.sym (singleSubstLemma n σ F)) [σFₙ]'
      [σFₙ'] = irrelevance' (PE.sym (singleSubstLemma n' σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σn'])))
      [Fₙ≡Fₙ'] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                (PE.sym (singleSubstLemma n' σ F)) [σFₙ]' [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn])))
                                        ([σ] , [σn'])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σn']))
      [σ'm'] = neuTerm [σ'ℕ] neM' ⊢m'
      [σ'm]' , [σ'm≡σ'm'] = redSubst*Term (redₜ d') [σ'ℕ] [σ'm']
      [σ'F'ₘ]' = proj₁ ([F'] ⊢Δ ([σ'] , [σ'm]))
      [σ'F'ₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F')) [σ'F'ₘ]'
      [σ'Fₘ]' = proj₁ ([F] ⊢Δ ([σ'] , [σ'm]))
      [σ'Fₘ] = irrelevance' (PE.sym (singleSubstLemma m σ' F)) [σ'Fₘ]'
      [σ'F'ₘ'] = irrelevance' (PE.sym (singleSubstLemma m' σ' F'))
                              (proj₁ ([F'] ⊢Δ ([σ'] , [σ'm'])))
      [F'ₘ≡F'ₘ'] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F'))
                                   (PE.sym (singleSubstLemma m' σ' F'))
                                   [σ'F'ₘ]' [σ'F'ₘ]
                                   ((proj₂ ([F'] ⊢Δ ([σ'] , [σ'm])))
                                           ([σ'] , [σ'm'])
                                           (reflSubst [Γ] ⊢Δ [σ'] , [σ'm≡σ'm']))
      [σFₙ≡σ'Fₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma n σ F))
                                   (PE.sym (singleSubstLemma m σ' F))
                                   [σFₙ]' [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ'] , [σ'm])
                                          ([σ≡σ'] , [σn≡σ'm]))
      [σ'Fₘ≡σ'F'ₘ] = irrelevanceEq'' (PE.sym (singleSubstLemma m σ' F))
                                     (PE.sym (singleSubstLemma m σ' F'))
                                     (proj₁ ([F] ⊢Δ ([σ'] , [σ'm])))
                                     [σ'Fₘ] ([F≡F'] ⊢Δ ([σ'] , [σ'm]))
      [σFₙ≡σ'F'ₘ] = transEq [σFₙ] [σ'Fₘ] [σ'F'ₘ] [σFₙ≡σ'Fₘ] [σ'Fₘ≡σ'F'ₘ]
      [σFₙ'≡σ'Fₘ'] = transEq [σFₙ'] [σFₙ] [σ'F'ₘ'] (symEq [σFₙ] [σFₙ'] [Fₙ≡Fₙ'])
                             (transEq [σFₙ] [σ'F'ₘ] [σ'F'ₘ'] [σFₙ≡σ'F'ₘ] [F'ₘ≡F'ₘ'])
      natrecN = neuTerm [σFₙ'] (natrec neN') (natrec ⊢F ⊢z ⊢s ⊢n')
      natrecM = neuTerm [σ'F'ₘ'] (natrec neM') (natrec ⊢F' ⊢z' ⊢s' ⊢m')
      natrecN≡M =
        convEqTerm₂ [σFₙ] [σFₙ'] [Fₙ≡Fₙ']
          (neuEqTerm [σFₙ'] (natrec neN') (natrec neM')
                     (natrec ⊢F ⊢z ⊢s ⊢n'
                     , conv (natrec ⊢F' ⊢z' ⊢s' ⊢m')
                            (sym (wellformedEq [σFₙ'] [σFₙ'≡σ'Fₘ']))
                     , natrec-cong ⊢F≡F' ⊢z≡z' ⊢s≡s'
                                   (PE.subst₂ (λ x y → _ ⊢ x ≡ y ∷ _)
                                              n''≡n' m''≡m' prop₂)))
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σn']
                     (λ {t} {t'} [t] [t'] [t≡t'] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstLemma t σ F))
                                  (PE.sym (singleSubstLemma t' σ F))
                                  (wellformedEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t'])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t']))))
      reduction₂ = natrec-subst* ⊢F' ⊢z' ⊢s' (redₜ d') [σ'ℕ] [σ'm']
                     (λ {t} {t'} [t] [t'] [t≡t'] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstLemma t σ' F'))
                                  (PE.sym (singleSubstLemma t' σ' F'))
                                  (wellformedEq (proj₁ ([F'] ⊢Δ ([σ'] , [t])))
                                               (proj₂ ([F'] ⊢Δ ([σ'] , [t]))
                                                      ([σ'] , [t'])
                                                      (reflSubst [Γ] ⊢Δ [σ'] , [t≡t']))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₙ'] [Fₙ≡Fₙ'] natrecN))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ'F'ₘ]
                                 (convTerm₂ [σ'F'ₘ] [σ'F'ₘ'] [F'ₘ≡F'ₘ'] natrecM))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] natrecN≡M
                               (convEqTerm₂ [σFₙ] [σ'F'ₘ] [σFₙ≡σ'F'ₘ]
                                            (symEqTerm [σ'F'ₘ] eq₂)))
-- Refuting cases
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ .zero d₁ zero prop₁)
                (ℕₜ₌ _ _ d₂ d' t≡u (suc prop₂)) =
  ⊥-elim (zero≢suc (whrDet* (redₜ d₁ , zero) (redₜ d' , suc)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ n d₁ (ne x) prop₁)
                (ℕₜ₌ _ _ d₂ d' t≡u (suc prop₂)) =
  ⊥-elim (suc≢ne x (whrDet* (redₜ d' , suc) (redₜ d₁ , ne x)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ .zero d zero prop) [σm]
                (ℕₜ₌ _ _ d₁ d' t≡u (suc prop₂)) =
  ⊥-elim (zero≢suc (whrDet* (redₜ d , zero) (redₜ d₁ , suc)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ n d (ne x) prop) [σm]
                (ℕₜ₌ _ _ d₁ d' t≡u (suc prop₂)) =
  ⊥-elim (suc≢ne x (whrDet* (redₜ d₁ , suc) (redₜ d , ne x)))

natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ _ d suc prop) [σm]
                (ℕₜ₌ .zero .zero d₂ d' t≡u zero) =
  ⊥-elim (zero≢suc (whrDet* (redₜ d₂ , zero) (redₜ d , suc)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ _ d₁ suc prop₁)
                (ℕₜ₌ .zero .zero d₂ d' t≡u zero) =
  ⊥-elim (zero≢suc (whrDet* (redₜ d' , zero) (redₜ d₁ , suc)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ n d₁ (ne x) prop₁)
                (ℕₜ₌ .zero .zero d₂ d' t≡u zero) =
  ⊥-elim (zero≢ne x (whrDet* (redₜ d' , zero) (redₜ d₁ , ne x)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ n d (ne x) prop) [σm]
                (ℕₜ₌ .zero .zero d₂ d' t≡u zero) =
  ⊥-elim (zero≢ne x (whrDet* (redₜ d₂ , zero) (redₜ d , ne x)))

natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ _ d suc prop) [σm]
                (ℕₜ₌ n₁ n' d₂ d' t≡u (ne x x₁ prop₂)) =
  ⊥-elim (suc≢ne x (whrDet* (redₜ d , suc) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                (ℕₜ .zero d zero prop) [σm]
                (ℕₜ₌ n₁ n' d₂ d' t≡u (ne x x₁ prop₂)) =
  ⊥-elim (zero≢ne x (whrDet* (redₜ d , zero) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ _ d₁ suc prop₁)
                (ℕₜ₌ n₁ n' d₂ d' t≡u (ne x₁ x₂ prop₂)) =
  ⊥-elim (suc≢ne x₂ (whrDet* (redₜ d₁ , suc) (redₜ d' , ne x₂)))
natrec-congTerm [Γ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
                [z] [z'] [z≡z'] [s] [s'] [s≡s'] ⊢Δ [σ] [σ'] [σ≡σ']
                [σn] (ℕₜ .zero d₁ zero prop₁)
                (ℕₜ₌ n₁ n' d₂ d' t≡u (ne x₁ x₂ prop₂)) =
  ⊥-elim (zero≢ne x₂ (whrDet* (redₜ d₁ , zero) (redₜ d' , ne x₂)))

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
natrecₛ {F} {z} {s} {n} [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]' = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = ¹} [Γ] (ℕₛ [Γ])) [F]
      [σn]' = irrelevanceTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      n' = subst σ n
      eqPrf = PE.trans (singleSubstLemma n' σ F)
                       (PE.sym (PE.trans (substCompEq F)
                               (substEq substConcatSingleton' F)))
  in  irrelevanceTerm' eqPrf (irrelevance' (PE.sym (singleSubstLemma n' σ F))
                                           (proj₁ ([F]' ⊢Δ ([σ] , [σn]'))))
                        (proj₁ ([Fₙ] ⊢Δ [σ]))
                   (natrecTerm {F} {z} {s} {n'} {σ = σ} [Γ]
                               [F]'
                               [F₀] [F₊] [z] [s] ⊢Δ [σ]
                               [σn]')
 ,   (λ {σ'} [σ'] [σ≡σ'] →
        let [σ'n]' = irrelevanceTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ']))
                                     (ℕ (idRed:*: (ℕ ⊢Δ)))
                                     (proj₁ ([n] ⊢Δ [σ']))
            [σn≡σ'n] = irrelevanceEqTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ]))
                                         (ℕ (idRed:*: (ℕ ⊢Δ)))
                                         (proj₂ ([n] ⊢Δ [σ]) [σ'] [σ≡σ'])
        in  irrelevanceEqTerm' eqPrf
              (irrelevance' (PE.sym (singleSubstLemma n' σ F))
                            (proj₁ ([F]' ⊢Δ ([σ] , [σn]'))))
              (proj₁ ([Fₙ] ⊢Δ [σ]))
              (natrec-congTerm {F} {F} {z} {z} {s} {s} {n'} {subst σ' n} {σ = σ}
                               [Γ] [F]' [F]' (reflₛ {F} (_∙_ {A = ℕ} {l = ¹}
                               [Γ] (ℕₛ [Γ])) [F]') [F₀] [F₀]
                               (reflₛ {F [ zero ]} [Γ] [F₀]) [F₊] [F₊]
                               (reflₛ {Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)}
                                      [Γ] [F₊])
                               [z] [z] (reflₜₛ {F [ zero ]} {z} [Γ] [F₀] [z])
                               [s] [s]
                               (reflₜₛ {Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)} {s}
                                       [Γ] [F₊] [s])
                               ⊢Δ [σ] [σ'] [σ≡σ'] [σn]' [σ'n]' [σn≡σ'n]))

natrec-congₛ : ∀ {F F' z z' s s' n n' Γ} ([Γ] : ⊩ₛ Γ)
          ([ℕ]  : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F / [Γ] ∙ [ℕ])
          ([F']  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F' / [Γ] ∙ [ℕ])
          ([F≡F']  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F ≡ F' / [Γ] ∙ [ℕ] / [F])
          ([F₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] / [Γ])
          ([F'₀] : Γ ⊩ₛ⟨ ¹ ⟩ F' [ zero ] / [Γ])
          ([F₀≡F'₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] ≡ F' [ zero ] / [Γ] / [F₀])
          ([F₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
          ([F'₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑) / [Γ])
          ([F₊≡F'₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                              ≡ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑) / [Γ]
                              / [F₊])
          ([Fₙ] : Γ ⊩ₛ⟨ ¹ ⟩ F [ n ] / [Γ])
          ([z] : Γ ⊩ₛ⟨ ¹ ⟩t z ∷ F [ zero ] / [Γ] / [F₀])
          ([z'] : Γ ⊩ₛ⟨ ¹ ⟩t z' ∷ F' [ zero ] / [Γ] / [F'₀])
          ([z≡z'] : Γ ⊩ₛ⟨ ¹ ⟩t' z ≡ z' ∷ F [ zero ] / [Γ] / [F₀])
          ([s] : Γ ⊩ₛ⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊])
          ([s'] : Γ ⊩ₛ⟨ ¹ ⟩t s' ∷ Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑) / [Γ]
                           / [F'₊])
          ([s≡s'] : Γ ⊩ₛ⟨ ¹ ⟩t' s ≡ s' ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                             / [Γ] / [F₊])
          ([n] : Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ])
          ([n'] : Γ ⊩ₛ⟨ ¹ ⟩t n' ∷ ℕ / [Γ] / [ℕ])
          ([n≡n'] : Γ ⊩ₛ⟨ ¹ ⟩t' n ≡ n' ∷ ℕ / [Γ] / [ℕ])
        → Γ ⊩ₛ⟨ ¹ ⟩t' natrec F z s n ≡ natrec F' z' s' n' ∷ F [ n ] / [Γ] / [Fₙ]
natrec-congₛ {F} {F'} {z} {z'} {s} {s'} {n} {n'}
             [Γ] [ℕ] [F] [F'] [F≡F'] [F₀] [F'₀] [F₀≡F'₀] [F₊] [F'₊] [F₊≡F'₊]
             [Fₙ] [z] [z'] [z≡z'] [s] [s'] [s≡s'] [n] [n']
             [n≡n'] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]' = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = ¹} [Γ] (ℕₛ [Γ])) [F]
      [F']' = S.irrelevance {A = F'} (_∙_ {A = ℕ} [Γ] [ℕ])
                            (_∙_ {l = ¹} [Γ] (ℕₛ [Γ])) [F']
      [F≡F']' = S.irrelevanceEq {A = F} {B = F'} (_∙_ {A = ℕ} [Γ] [ℕ])
                                (_∙_ {l = ¹} [Γ] (ℕₛ [Γ])) [F] [F]' [F≡F']
      [σn]' = irrelevanceTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      [σn']' = irrelevanceTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ]))
                               (ℕ (idRed:*: (ℕ ⊢Δ))) (proj₁ ([n'] ⊢Δ [σ]))
      [σn≡σn']' = irrelevanceEqTerm {l' = ¹} (proj₁ ([ℕ] ⊢Δ [σ]))
                                    (ℕ (idRed:*: (ℕ ⊢Δ))) ([n≡n'] ⊢Δ [σ])
      [Fₙ]' = irrelevance' (PE.sym (singleSubstLemma (subst σ n) σ F))
                           (proj₁ ([F]' ⊢Δ ([σ] , [σn]')))
  in  irrelevanceEqTerm' (PE.sym (singleSubstLift F n))
                         [Fₙ]' (proj₁ ([Fₙ] ⊢Δ [σ]))
                         (natrec-congTerm {F} {F'} {z} {z'} {s} {s'}
                                          {subst σ n} {subst σ n'}
                                          [Γ] [F]' [F']' [F≡F']'
                                          [F₀] [F'₀] [F₀≡F'₀]
                                          [F₊] [F'₊] [F₊≡F'₊]
                                          [z] [z'] [z≡z']
                                          [s] [s'] [s≡s'] ⊢Δ
                                          [σ] [σ] (reflSubst [Γ] ⊢Δ [σ])
                                          [σn]' [σn']' [σn≡σn']')
