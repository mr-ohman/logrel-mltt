{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Natrec {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    m : Nat
    Γ Δ : Con Term m

-- Natural recursion closure reduction (requires reducible terms and equality).
natrec-subst* : ∀ {C c g n n′ l} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
              → Γ ⊢ g ∷ Π ℕ ▹ (C ▹▹ C [ suc (var x0) ]↑)
              → Γ ⊢ n ⇒* n′ ∷ ℕ
              → ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
              → Γ ⊩⟨ l ⟩ n′ ∷ ℕ / [ℕ]
              → (∀ {t t′} → Γ ⊩⟨ l ⟩ t  ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t′ ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t ≡ t′ ∷ ℕ / [ℕ]
                          → Γ ⊢ C [ t ] ≡ C [ t′ ])
              → Γ ⊢ natrec C c g n ⇒* natrec C c g n′ ∷ C [ n ]
natrec-subst* C c g (id x) [ℕ] [n′] prop = id (natrecⱼ C c g x)
natrec-subst* C c g (x ⇨ n⇒n′) [ℕ] [n′] prop =
  let q , w = redSubst*Term n⇒n′ [ℕ] [n′]
      a , s = redSubstTerm x [ℕ] q
  in  natrec-subst C c g x ⇨ conv* (natrec-subst* C c g n⇒n′ [ℕ] [n′] prop)
                   (prop q a (symEqTerm [ℕ] s))

-- Helper functions for construction of valid type for the successor case of natrec.

sucCase₃ : ∀ {Γ : Con Term m} {l} ([Γ] : ⊩ᵛ_ {m} Γ)
           ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
         → Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ suc (var x0) ∷ ℕ / [Γ] ∙ [ℕ]
                 / (λ {_} {Δ} {σ} → wk1ᵛ {A = ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ = Δ} {σ})
sucCase₃ {Γ = Γ} {l} [Γ] [ℕ] {Δ = Δ} {σ} =
  sucᵛ {n = var x0} {l = l} (_∙_ {A = ℕ} [Γ] [ℕ])
       (λ {_} {Δ} {σ} → wk1ᵛ {A = ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ = Δ} {σ})
       (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ′] [σ≡σ′] → proj₂ [σ≡σ′])) {Δ = Δ} {σ}

sucCase₂ : ∀ {F l} ([Γ] : ⊩ᵛ Γ)
           ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
           ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
         → Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F [ suc (var x0) ]↑ / [Γ] ∙ [ℕ]
sucCase₂ {Γ = Γ} {F} {l} [Γ] [ℕ] [F] =
  subst↑S {F = ℕ} {F} {suc (var x0)} [Γ] [ℕ] [F]
          (λ {_} {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ = Δ} {σ})

sucCase₁ : ∀ {F l} ([Γ] : ⊩ᵛ Γ)
           ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
           ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
         → Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ▹▹ F [ suc (var x0) ]↑ / [Γ] ∙ [ℕ]
sucCase₁ {Γ = Γ} {F} {l} [Γ] [ℕ] [F] =
  ▹▹ᵛ {F = F} {F [ suc (var x0) ]↑} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]
      (sucCase₂ {F = F} [Γ] [ℕ] [F])

-- Construct a valid type for the successor case of natrec.
sucCase : ∀ {F l} ([Γ] : ⊩ᵛ Γ)
          ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
          ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
        → Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ]
sucCase {Γ = Γ} {F} {l} [Γ] [ℕ] [F] =
  Πᵛ {F = ℕ} {F ▹▹ F [ suc (var x0) ]↑} [Γ] [ℕ]
     (sucCase₁ {F = F} [Γ] [ℕ] [F])

-- Construct a valid type equality for the successor case of natrec.
sucCaseCong : ∀ {F F′ l} ([Γ] : ⊩ᵛ Γ)
              ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
              ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
              ([F′] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F′ / [Γ] ∙ [ℕ])
              ([F≡F′] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] ∙ [ℕ] / [F])
        → Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F  ▹▹ F  [ suc (var x0) ]↑)
                  ≡ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑)
                  / [Γ] / sucCase {F = F} [Γ] [ℕ] [F]
sucCaseCong {Γ = Γ} {F} {F′} {l} [Γ] [ℕ] [F] [F′] [F≡F′] =
  Π-congᵛ {F = ℕ} {F ▹▹ F [ suc (var x0) ]↑} {ℕ} {F′ ▹▹ F′ [ suc (var x0) ]↑}
          [Γ] [ℕ] (sucCase₁ {F = F} [Γ] [ℕ] [F]) [ℕ] (sucCase₁ {F = F′} [Γ] [ℕ] [F′])
          (reflᵛ {A = ℕ} [Γ] [ℕ])
          (▹▹-congᵛ {F = F} {F′} {F [ suc (var x0) ]↑} {F′ [ suc (var x0) ]↑}
             (_∙_ {A = ℕ} [Γ] [ℕ]) [F] [F′] [F≡F′]
             (sucCase₂ {F = F} [Γ] [ℕ] [F]) (sucCase₂ {F = F′} [Γ] [ℕ] [F′])
             (subst↑SEq {F = ℕ} {F} {F′} {suc (var x0)} {suc (var x0)}
                        [Γ] [ℕ] [F] [F′] [F≡F′]
                        (λ {_} {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ = Δ} {σ})
                        (λ {_} {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ = Δ} {σ})
                        (λ {_} {Δ} {σ} →
                           reflᵗᵛ {A = ℕ} {suc (var x0)} (_∙_ {A = ℕ} [Γ] [ℕ])
                                  (λ {_} {Δ} {σ} → wk1ᵛ {A = ℕ} {ℕ} [Γ] [ℕ] [ℕ] {Δ = Δ} {σ})
                                  (λ {_} {Δ} {σ} → sucCase₃ [Γ] [ℕ] {Δ = Δ} {σ})
                           {Δ = Δ} {σ})))

-- Reducibility of natural recursion under a valid substitution.
natrecTerm : ∀ {F z s n σ l}
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
             ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
             ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ])
             ([z]  : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
             ([s]  : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                       / [Γ] / [F₊])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
           → Δ ⊩⟨ l ⟩ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n
               ∷ subst (liftSubst σ) F [ n ]
               / irrelevance′ (PE.sym (singleSubstComp n σ F))
                              (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrecTerm {Γ = Γ} {Δ = Δ} {F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .(suc m) d n≡n (sucᵣ {m} [m])) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢m = escapeTerm {l = l} [σℕ] [m]
      [σsm] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                              (ℕₜ (suc m) (idRedTerm:*: (sucⱼ ⊢m)) n≡n (sucᵣ [m]))
      [σn] = ℕₜ (suc m) d n≡n (sucᵣ [m])
      [σn]′ , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₘ] = irrelevance′ (PE.sym (singleSubstComp (suc m) σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [Fₙ≡Fₛₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                 (PE.sym (singleSubstComp (suc m) σ F))
                                 [σFₙ]′ [σFₙ]
                                 (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsm]))
      [σFₘ] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                             (substSingletonComp F)))
                           (proj₁ ([F] ⊢Δ ([σ] , [m])))
      [σFₛₘ]′ = irrelevance′ (natrecIrrelevantSubst F z s m σ)
                             (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [σF₊ₘ] = substSΠ₁ BΠ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [m]
      natrecM = appTerm [σFₘ] [σFₛₘ]′ [σF₊ₘ]
                        (appTerm [σℕ] [σF₊ₘ]
                                 (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [m])
                        (natrecTerm {F = F} {z} {s} {m} {σ = σ}
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [m])
      natrecM′ = irrelevanceTerm′ (PE.trans
                                    (PE.sym (natrecIrrelevantSubst F z s m σ))
                                    (PE.sym (singleSubstComp (suc m) σ F)))
                                  [σFₛₘ]′ [σFₛₘ] natrecM
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsm]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
                  ⇨∷* (conv* (natrec-suc ⊢m ⊢F ⊢z ⊢s
                              ⇨ id (escapeTerm [σFₛₘ] natrecM′))
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡Fₛₘ]))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₛₘ] [Fₙ≡Fₛₘ] natrecM′))
natrecTerm {Γ = Γ} {Δ = Δ} {F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .zero d n≡n zeroᵣ) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      ⊢F = escape [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      [σ0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                             (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) n≡n zeroᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σn] = ℕₜ zero d n≡n zeroᵣ
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0])
                       (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero σ F)))
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀] [σz]))
natrecTerm {Γ = Γ} {Δ = Δ} {F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      [σn] = ℕₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x) (natrecSucCase σ F)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      [σm] = neuTerm [σℕ] neM ⊢m m≡m
      [σn]′ , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₘ] = irrelevance′ (PE.sym (singleSubstComp m σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σm])))
      [Fₙ≡Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp m σ F)) [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn]))) ([σ] , [σm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σm]))
      natrecM = neuTerm [σFₘ] (natrecₙ neM) (natrecⱼ ⊢F ⊢z ⊢s ⊢m)
                        (~-natrec ⊢F≡F ⊢z≡z ⊢s≡s m≡m)
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σm]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₘ] [Fₙ≡Fₘ] natrecM))


-- Reducibility of natural recursion congruence under a valid substitution equality.
natrec-congTerm : ∀ {F F′ z z′ s s′ n m σ σ′ l}
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
                  ([F′]     : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F′ / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
                  ([F≡F′]   : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ F′ / _∙_ {l = l} [Γ] (ℕᵛ [Γ])
                                    / [F])
                  ([F₀]     : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
                  ([F′₀]    : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero ] / [Γ])
                  ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] ≡ F′ [ zero ] / [Γ] / [F₀])
                  ([F₊]     : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                                / [Γ])
                  ([F′₊]    : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑)
                                / [Γ])
                  ([F₊≡F₊′] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                                ≡ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑)
                                / [Γ] / [F₊])
                  ([z]      : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
                  ([z′]     : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero ] / [Γ] / [F′₀])
                  ([z≡z′]   : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero ] / [Γ] / [F₀])
                  ([s]      : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                                / [Γ] / [F₊])
                  ([s′]     : Γ ⊩ᵛ⟨ l ⟩ s′
                                ∷ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑)
                                / [Γ] / [F′₊])
                  ([s≡s′]   : Γ ⊩ᵛ⟨ l ⟩ s ≡ s′
                                ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                                / [Γ] / [F₊])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                → Δ ⊩⟨ l ⟩ natrec (subst (liftSubst σ) F)
                                  (subst σ z) (subst σ s) n
                    ≡ natrec (subst (liftSubst σ′) F′)
                             (subst σ′ z′) (subst σ′ s′) m
                    ∷ subst (liftSubst σ) F [ n ]
                    / irrelevance′ (PE.sym (singleSubstComp n σ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrec-congTerm {Γ = Γ} {Δ = Δ} {F} {F′} {z} {z′} {s} {s′} {n} {m} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ .(suc n′) d n≡n (sucᵣ {n′} [n′]))
                (ℕₜ .(suc m′) d′ m≡m (sucᵣ {m′} [m′]))
                (ℕₜ₌ .(suc n″) .(suc m″) d₁ d₁′
                     t≡u (sucᵣ {n″} {m″} [n″≡m″])) =
  let n″≡n′ = suc-PE-injectivity (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d , sucₙ))
      m″≡m′ = suc-PE-injectivity (whrDet*Term (redₜ d₁′ , sucₙ) (redₜ d′ , sucₙ))
      [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ′ℕ] = proj₁ ([ℕ] ⊢Δ [σ′])
      [n′≡m′] = irrelevanceEqTerm″ n″≡n′ m″≡m′ PE.refl [σℕ] [σℕ] [n″≡m″]
      [σn] = ℕₜ (suc n′) d n≡n (sucᵣ [n′])
      [σ′m] = ℕₜ (suc m′) d′ m≡m (sucᵣ [m′])
      [σn≡σ′m] = ℕₜ₌ (suc n″) (suc m″) d₁ d₁′ t≡u (sucᵣ [n″≡m″])
      ⊢ℕ = escape [σℕ]
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n′ = escapeTerm {l = l} [σℕ] [n′]
      ⊢ℕ′ = escape [σ′ℕ]
      ⊢F′ = escape (proj₁ ([F′] (⊢Δ ∙ ⊢ℕ′)
                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                    (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x) (natrecSucCase σ′ F′)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                    (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢m′ = escapeTerm {l = l} [σ′ℕ] [m′]
      [σsn′] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                               (ℕₜ (suc n′) (idRedTerm:*: (sucⱼ ⊢n′)) n≡n (sucᵣ [n′]))
      [σn]′ , [σn≡σsn′] = redSubst*Term (redₜ d) [σℕ] [σsn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₙ′] = irrelevance′ (PE.sym (singleSubstComp (suc n′) σ F))
                             (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [Fₙ≡Fₛₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.sym (singleSubstComp (suc n′) σ F))
                                  [σFₙ]′ [σFₙ]
                                  (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                         (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [Fₙ≡Fₛₙ′]′ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (natrecIrrelevantSubst F z s n′ σ)
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                          (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [σFₙ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                              (substSingletonComp F)))
                            (proj₁ ([F] ⊢Δ ([σ] , [n′])))
      [σFₛₙ′]′ = irrelevance′ (natrecIrrelevantSubst F z s n′ σ)
                              (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [σF₊ₙ′] = substSΠ₁ BΠ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [n′]
      [σ′sm′] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σ′ℕ]
                                (ℕₜ (suc m′) (idRedTerm:*: (sucⱼ ⊢m′)) m≡m (sucᵣ [m′]))
      [σ′m]′ , [σ′m≡σ′sm′] = redSubst*Term (redₜ d′) [σ′ℕ] [σ′sm′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₛₘ′] = irrelevance′ (PE.sym (singleSubstComp (suc m′) σ′ F′))
                               (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [F′ₘ≡F′ₛₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.sym (singleSubstComp (suc m′) σ′ F′))
                                    [σ′F′ₘ]′ [σ′F′ₘ]
                                    (proj₂ ([F′] ⊢Δ ([σ′] , [σ′m]))
                                           ([σ′] , [σ′sm′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′sm′]))
      [σ′Fₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                               (substSingletonComp F)))
                             (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F′)
                                                (substSingletonComp F′)))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₛₘ′]′ = irrelevance′ (natrecIrrelevantSubst F′ z′ s′ m′ σ′)
                                (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [σ′F′₊ₘ′] = substSΠ₁ BΠ (proj₁ ([F′₊] ⊢Δ [σ′])) [σ′ℕ] [m′]
      [σFₙ′≡σ′Fₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp n′ σ F))
                                     (PE.sym (singleSubstComp m′ σ′ F))
                                     (proj₁ ([F] ⊢Δ ([σ] , [n′]))) [σFₙ′]
                                     (proj₂ ([F] ⊢Δ ([σ] , [n′]))
                                            ([σ′] , [m′]) ([σ≡σ′] , [n′≡m′]))
      [σ′Fₘ′≡σ′F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m′ σ′ F))
                                       (PE.sym (singleSubstComp m′ σ′ F′))
                                       (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
                                       [σ′Fₘ′] ([F≡F′] ⊢Δ ([σ′] , [m′]))
      [σFₙ′≡σ′F′ₘ′] = transEq [σFₙ′] [σ′Fₘ′] [σ′F′ₘ′] [σFₙ′≡σ′Fₘ′] [σ′Fₘ′≡σ′F′ₘ′]
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn]))) [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn]))
                                          ([σ′] , [σ′m]) ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      natrecN = appTerm [σFₙ′] [σFₛₙ′]′ [σF₊ₙ′]
                        (appTerm [σℕ] [σF₊ₙ′] (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [n′])
                        (natrecTerm {F = F} {z} {s} {n′} {σ = σ}
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n′])
      natrecN′ = irrelevanceTerm′ (PE.trans (PE.sym (natrecIrrelevantSubst F z s n′ σ))
                                            (PE.sym (singleSubstComp (suc n′) σ F)))
                                  [σFₛₙ′]′ [σFₛₙ′] natrecN
      natrecM = appTerm [σ′F′ₘ′] [σ′F′ₛₘ′]′ [σ′F′₊ₘ′]
                        (appTerm [σ′ℕ] [σ′F′₊ₘ′] (proj₁ ([F′₊] ⊢Δ [σ′]))
                                 (proj₁ ([s′] ⊢Δ [σ′])) [m′])
                        (natrecTerm {F = F′} {z′} {s′} {m′} {σ = σ′}
                                    [Γ] [F′] [F′₀] [F′₊] [z′] [s′] ⊢Δ [σ′] [m′])
      natrecM′ = irrelevanceTerm′ (PE.trans (PE.sym (natrecIrrelevantSubst F′ z′ s′ m′ σ′))
                                            (PE.sym (singleSubstComp (suc m′) σ′ F′)))
                                  [σ′F′ₛₘ′]′ [σ′F′ₛₘ′] natrecM
      [σs≡σ′s] = proj₂ ([s] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′s≡σ′s′] = convEqTerm₂ (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([F₊] ⊢Δ [σ′]))
                               (proj₂ ([F₊] ⊢Δ [σ]) [σ′] [σ≡σ′]) ([s≡s′] ⊢Δ [σ′])
      [σs≡σ′s′] = transEqTerm (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ′s] [σ′s≡σ′s′]
      appEq = convEqTerm₂ [σFₙ] [σFₛₙ′]′ [Fₙ≡Fₛₙ′]′
                (app-congTerm [σFₙ′] [σFₛₙ′]′ [σF₊ₙ′]
                  (app-congTerm [σℕ] [σF₊ₙ′] (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ′s′]
                                [n′] [m′] [n′≡m′])
                  (natrecTerm {F = F} {z} {s} {n′} {σ = σ}
                              [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n′])
                  (convTerm₂ [σFₙ′] [σ′F′ₘ′] [σFₙ′≡σ′F′ₘ′]
                             (natrecTerm {F = F′} {z′} {s′} {m′} {σ = σ′}
                                         [Γ] [F′] [F′₀] [F′₊] [z′] [s′]
                                         ⊢Δ [σ′] [m′]))
                  (natrec-congTerm {F = F} {F′} {z} {z′} {s} {s′} {n′} {m′} {σ = σ}
                                   [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀]
                                   [F₊] [F′₊] [F₊≡F′₊] [z] [z′] [z≡z′]
                                   [s] [s′] [s≡s′]
                                   ⊢Δ [σ] [σ′] [σ≡σ′] [n′] [m′] [n′≡m′]))
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                   ⇨∷* (conv* (natrec-suc ⊢n′ ⊢F ⊢z ⊢s
                   ⇨   id (escapeTerm [σFₛₙ′] natrecN′))
                          (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡Fₛₙ′]))))
      reduction₂ = natrec-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ] [σ′sm′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                   ⇨∷* (conv* (natrec-suc ⊢m′ ⊢F′ ⊢z′ ⊢s′
                   ⇨   id (escapeTerm [σ′F′ₛₘ′] natrecM′))
                          (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′ₛₘ′]))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₛₙ′]
                                            [Fₙ≡Fₛₙ′] natrecN′))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₛₘ′]
                                            [F′ₘ≡F′ₛₘ′] natrecM′))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] appEq
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
natrec-congTerm {Γ = Γ} {Δ = Δ} {F} {F′} {z} {z′} {s} {s′} {n} {m} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ .zero d n≡n zeroᵣ) (ℕₜ .zero d₁ m≡m zeroᵣ)
                (ℕₜ₌ .zero .zero d₂ d′ t≡u zeroᵣ) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                 (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢F′ = escape (proj₁ ([F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ)
                                   (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x) (natrecSucCase σ′ F′)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      [σ0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ]))
                             (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) n≡n zeroᵣ)
      [σ′0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ′]))
                              (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) m≡m zeroᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σ′m]′ , [σ′m≡σ′0] = redSubst*Term (redₜ d′) (proj₁ ([ℕ] ⊢Δ [σ′])) [σ′0]
      [σn] = ℕₜ zero d n≡n zeroᵣ
      [σ′m] = ℕₜ zero d′ m≡m zeroᵣ
      [σn≡σ′m] = ℕₜ₌ zero zero d₂ d′ t≡u zeroᵣ
      [σn≡σ′0] = transEqTerm [σℕ] [σn≡σ′m] [σ′m≡σ′0]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σFₙ≡σ′F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′0]) ([σ≡σ′] , [σn≡σ′0])
      [σFₙ≡σ′F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [σFₙ≡σ′F₀]′
      [F′ₘ≡F′₀]′ = proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])) ([σ′] , [σ′0])
                         (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′0])
      [F′ₘ≡F′₀] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                  (PE.sym (substCompEq F′))
                                  [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero σ F)))
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [F′ₘ≡F′₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.trans (substConcatSingleton′ F′)
                                              (PE.sym (singleSubstComp zero σ′ F′)))
                                    [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      [σ′z′] = proj₁ ([z′] ⊢Δ [σ′])
      [σz≡σ′z] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀]
                             (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′])
      [σ′z≡σ′z′] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ′])) [σFₙ≡σ′F₀]
                               ([z≡z′] ⊢Δ [σ′])
      [σz≡σ′z′] = transEqTerm [σFₙ] [σz≡σ′z] [σ′z≡σ′z′]
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
      reduction₂ = natrec-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) (proj₁ ([ℕ] ⊢Δ [σ′])) [σ′0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ′ F′))
                                 (PE.sym (singleSubstComp t′ σ′ F′))
                                 (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                              (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                     ([σ′] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F′ ⊢z′ ⊢s′ ⇨ id ⊢z′)
                             (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′₀]″))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ]))
                                            [Fₙ≡F₀] [σz]))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] (proj₁ ([F′₀] ⊢Δ [σ′]))
                                            [F′ₘ≡F′₀] [σ′z′]))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] [σz≡σ′z′]
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
natrec-congTerm {Γ = Γ} {Δ = Δ} {F} {F′} {z} {z′} {s} {s′} {n} {m} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (ℕₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                (ℕₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))) =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ′ℕ] = proj₁ ([ℕ] ⊢Δ [σ′])
      [σn] = ℕₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁))
      [σ′m] = ℕₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁))
      [σn≡σ′m] = ℕₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ′F] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      [σ′F′] = proj₁ ([F′] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x) (natrecSucCase σ F)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢z′≡z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F′ zero)
                        (escapeTermEq (proj₁ ([F′₀] ⊢Δ [σ′]))
                                          (reflEqTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                                      (proj₁ ([z′] ⊢Δ [σ′]))))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x) (natrecSucCase σ′ F′)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢s′≡s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ≅ subst σ′ s′ ∷ x) (natrecSucCase σ′ F′)
                      (escapeTermEq (proj₁ ([F′₊] ⊢Δ [σ′]))
                                        (reflEqTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                                    (proj₁ ([s′] ⊢Δ [σ′]))))
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                           (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
                                      {σ′ = liftSubst σ′}
                                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
                                      (liftSubstSEq {F = ℕ} [Γ] ⊢Δ [ℕ] [σ] [σ≡σ′]))
      ⊢σz≡σ′z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                         (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                          (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      ⊢σs≡σ′s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ′ s ∷ x)
                         (natrecSucCase σ F)
                         (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                          (proj₂ ([s] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      ⊢σ′F≡⊢σ′F′ = escapeEq [σ′F] ([F≡F′] (⊢Δ ∙ ⊢ℕ)
                               (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      ⊢σ′z≡⊢σ′z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x)
                            (singleSubstLift F zero)
                            (≅-conv (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ′]))
                                                   ([z≡z′] ⊢Δ [σ′]))
                                  (sym (≅-eq (escapeEq (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₂ ([F₀] ⊢Δ [σ]) [σ′] [σ≡σ′])))))
      ⊢σ′s≡⊢σ′s′ = PE.subst (λ x → Δ ⊢ subst σ′ s ≅ subst σ′ s′ ∷ x)
                            (natrecSucCase σ F)
                            (≅-conv (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ′]))
                                                   ([s≡s′] ⊢Δ [σ′]))
                                  (sym (≅-eq (escapeEq (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₂ ([F₊] ⊢Δ [σ]) [σ′] [σ≡σ′])))))
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡⊢σ′F′
      ⊢z≡z′ = ≅ₜ-trans ⊢σz≡σ′z ⊢σ′z≡⊢σ′z′
      ⊢s≡s′ = ≅ₜ-trans ⊢σs≡σ′s ⊢σ′s≡⊢σ′s′
      [σn′] = neuTerm [σℕ] neN′ ⊢n′ n≡n₁
      [σn]′ , [σn≡σn′] = redSubst*Term (redₜ d) [σℕ] [σn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₙ′] = irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σn′])))
      [Fₙ≡Fₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp n′ σ F)) [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn])))
                                        ([σ] , [σn′])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σn′]))
      [σ′m′] = neuTerm [σ′ℕ] neM′ ⊢m′ m≡m₁
      [σ′m]′ , [σ′m≡σ′m′] = redSubst*Term (redₜ d′) [σ′ℕ] [σ′m′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ′] = irrelevance′ (PE.sym (singleSubstComp m′ σ′ F′))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [σ′m′])))
      [F′ₘ≡F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                   (PE.sym (singleSubstComp m′ σ′ F′))
                                   [σ′F′ₘ]′ [σ′F′ₘ]
                                   ((proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])))
                                           ([σ′] , [σ′m′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′m′]))
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     (proj₁ ([F] ⊢Δ ([σ′] , [σ′m])))
                                     [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [σFₙ′≡σ′Fₘ′] = transEq [σFₙ′] [σFₙ] [σ′F′ₘ′] (symEq [σFₙ] [σFₙ′] [Fₙ≡Fₙ′])
                             (transEq [σFₙ] [σ′F′ₘ] [σ′F′ₘ′] [σFₙ≡σ′F′ₘ] [F′ₘ≡F′ₘ′])
      natrecN = neuTerm [σFₙ′] (natrecₙ neN′) (natrecⱼ ⊢F ⊢z ⊢s ⊢n′)
                        (~-natrec ⊢F≡F ⊢z≡z ⊢s≡s n≡n₁)
      natrecM = neuTerm [σ′F′ₘ′] (natrecₙ neM′) (natrecⱼ ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                        (~-natrec ⊢F′≡F′ ⊢z′≡z′ ⊢s′≡s′ m≡m₁)
      natrecN≡M =
        convEqTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′]
          (neuEqTerm [σFₙ′] (natrecₙ neN′) (natrecₙ neM′)
                     (natrecⱼ ⊢F ⊢z ⊢s ⊢n′)
                     (conv (natrecⱼ ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                            (sym (≅-eq (escapeEq [σFₙ′] [σFₙ′≡σ′Fₘ′]))))
                     (~-natrec ⊢F≡F′ ⊢z≡z′ ⊢s≡s′
                               (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _)
                                          n″≡n′ m″≡m′ prop₂)))
      reduction₁ = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
      reduction₂ = natrec-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ] [σ′m′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′] natrecN))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₘ′] [F′ₘ≡F′ₘ′] natrecM))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] natrecN≡M
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
-- Refuting cases
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ zeroᵣ)
                (ℕₜ₌ _ _ d₂ d′ t≡u (sucᵣ prop₂)) with whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕₜ₌ _ _ d₂ d′ t≡u (sucᵣ prop₂)) =
  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d′ , sucₙ) (redₜ d₁ , ne neK)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ zeroᵣ) [σm]
                (ℕₜ₌ _ _ d₁ d′ t≡u (sucᵣ prop₂)) with whrDet*Term (redₜ d , zeroₙ) (redₜ d₁ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕₜ₌ _ _ d₁ d′ t≡u (sucᵣ prop₂)) =
  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d , ne neK)))

natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ (sucᵣ prop)) [σm]
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) with whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ (sucᵣ prop₁))
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) with whrDet*Term (redₜ d′ , zeroₙ) (redₜ d₁ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) =
  ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d′ , zeroₙ) (redₜ d₁ , ne neK)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) =
  ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d , ne neK)))

natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ (sucᵣ prop)) [σm]
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) =
  ⊥-elim (suc≢ne x (whrDet*Term (redₜ d , sucₙ) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ zeroᵣ) [σm]
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) =
  ⊥-elim (zero≢ne x (whrDet*Term (redₜ d , zeroₙ) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ (sucᵣ prop₁))
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) =
  ⊥-elim (suc≢ne x₂ (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d′ , ne x₂)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ zeroᵣ)
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) =
  ⊥-elim (zero≢ne x₂ (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , ne x₂)))


-- Validity of natural recursion.
natrecᵛ : ∀ {F z s n l} ([Γ] : ⊩ᵛ Γ)
          ([ℕ]  : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
          ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] / [Γ])
        → Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀]
        → Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ] / [F₊]
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ])
        → Γ ⊩ᵛ⟨ l ⟩ natrec F z s n ∷ F [ n ] / [Γ] / [Fₙ]
natrecᵛ {F = F} {z} {s} {n} {l = l} [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      n′ = subst σ n
      eqPrf = PE.trans (singleSubstComp n′ σ F)
                       (PE.sym (PE.trans (substCompEq F)
                               (substConcatSingleton′ F)))
  in  irrelevanceTerm′ eqPrf (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
                        (proj₁ ([Fₙ] ⊢Δ [σ]))
                   (natrecTerm {F = F} {z} {s} {n′} {σ = σ} [Γ]
                               [F]′
                               [F₀] [F₊] [z] [s] ⊢Δ [σ]
                               [σn]′)
 ,   (λ {σ′} [σ′] [σ≡σ′] →
        let [σ′n]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ′]))
                                     (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                                     (proj₁ ([n] ⊢Δ [σ′]))
            [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                                         (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                                         (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
        in  irrelevanceEqTerm′ eqPrf
              (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
              (proj₁ ([Fₙ] ⊢Δ [σ]))
              (natrec-congTerm {F = F} {F} {z} {z} {s} {s} {n′} {subst σ′ n} {σ = σ}
                               [Γ] [F]′ [F]′ (reflᵛ {A = F} (_∙_ {A = ℕ} {l = l}
                               [Γ] (ℕᵛ [Γ])) [F]′) [F₀] [F₀]
                               (reflᵛ {A = F [ zero ]} [Γ] [F₀]) [F₊] [F₊]
                               (reflᵛ {A = Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)}
                                      [Γ] [F₊])
                               [z] [z] (reflᵗᵛ {A = F [ zero ]} {z} [Γ] [F₀] [z])
                               [s] [s]
                               (reflᵗᵛ {A = Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)} {s}
                                       [Γ] [F₊] [s])
                               ⊢Δ [σ] [σ′] [σ≡σ′] [σn]′ [σ′n]′ [σn≡σ′n]))

-- Validity of natural recursion congruence.
natrec-congᵛ : ∀ {F F′ z z′ s s′ n n′ l} ([Γ] : ⊩ᵛ Γ)
          ([ℕ]  : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
          ([F′]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F′ / [Γ] ∙ [ℕ])
          ([F≡F′]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] ∙ [ℕ] / [F])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
          ([F′₀] : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero ] / [Γ])
          ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] ≡ F′ [ zero ] / [Γ] / [F₀])
          ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ])
          ([F′₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑) / [Γ])
          ([F₊≡F′₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                              ≡ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑) / [Γ]
                              / [F₊])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] / [Γ])
          ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
          ([z′] : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero ] / [Γ] / [F′₀])
          ([z≡z′] : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero ] / [Γ] / [F₀])
          ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑) / [Γ] / [F₊])
          ([s′] : Γ ⊩ᵛ⟨ l ⟩ s′ ∷ Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑) / [Γ]
                           / [F′₊])
          ([s≡s′] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                             / [Γ] / [F₊])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ ℕ / [Γ] / [ℕ])
          ([n≡n′] : Γ ⊩ᵛ⟨ l ⟩ n ≡ n′ ∷ ℕ / [Γ] / [ℕ])
        → Γ ⊩ᵛ⟨ l ⟩ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] / [Γ] / [Fₙ]
natrec-congᵛ {F = F} {F′} {z} {z′} {s} {s′} {n} {n′} {l = l}
             [Γ] [ℕ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
             [Fₙ] [z] [z′] [z≡z′] [s] [s′] [s≡s′] [n] [n′]
             [n≡n′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F]
      [F′]′ = S.irrelevance {A = F′} (_∙_ {A = ℕ} [Γ] [ℕ])
                            (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F′]
      [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} (_∙_ {A = ℕ} [Γ] [ℕ])
                                (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F] [F]′ [F≡F′]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                               (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n′] ⊢Δ [σ]))
      [σn≡σn′]′ = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                                    (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) ([n≡n′] ⊢Δ [σ])
      [Fₙ]′ = irrelevance′ (PE.sym (singleSubstComp (subst σ n) σ F))
                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′)))
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift F n))
                         [Fₙ]′ (proj₁ ([Fₙ] ⊢Δ [σ]))
                         (natrec-congTerm {F = F} {F′} {z} {z′} {s} {s′}
                                          {subst σ n} {subst σ n′}
                                          [Γ] [F]′ [F′]′ [F≡F′]′
                                          [F₀] [F′₀] [F₀≡F′₀]
                                          [F₊] [F′₊] [F₊≡F′₊]
                                          [z] [z′] [z≡z′]
                                          [s] [s′] [s≡s′] ⊢Δ
                                          [σ] [σ] (reflSubst [Γ] ⊢Δ [σ])
                                          [σn]′ [σn′]′ [σn≡σn′]′)
