module Definition.Typed.Weakening where

open import Definition.Untyped as U hiding (wk) --; _⊆_; toWk; wkₜ; wkLiftₜ)
open import Definition.Untyped.Properties as UP using (wkIndex-step; wkIndex-lift; wk-β; wk-β-natrec)
open import Definition.Typed

open import Tools.Context

import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.HeterogeneousEquality as HE


-- Weakening type

mutual
  data _⊆_ : Con Term → Con Term → Set where
    base : ε ⊆ ε
    step : ∀ {Γ : Con Term} {Δ : Con Term} {σ} (inc : Γ ⊆ Δ) →  Γ      ⊆ (Δ ∙ σ)
    lift : ∀ {Γ : Con Term} {Δ : Con Term} {σ} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ U.wk (toWk inc) σ)

  toWk : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Wk
  toWk base = id
  toWk (step ρ) = step (toWk ρ)
  toWk (lift ρ) = lift (toWk ρ)

wkₜ : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Term → Term
wkₜ ρ = U.wk (toWk ρ)

wkLiftₜ : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Term → Term
wkLiftₜ ρ = U.wk (lift (toWk ρ))


-- Weakening composition

mutual
  _•ₜ_ : ∀ {Γ Δ E} → Δ ⊆ E → Γ ⊆ Δ → Γ ⊆ E
  base •ₜ η′ = η′
  step η •ₜ η′ = step (η •ₜ η′)
  lift η •ₜ step η′ = step (η •ₜ η′)
  lift η •ₜ lift η′ =  PE.subst (λ x → _ ∙ _ ⊆ _ ∙ x)
                               (wk-comp-comm η η′)
                               (lift (η •ₜ η′))

  wk-comp-comm : ∀ {Γ Δ E σ} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) → wkₜ (η •ₜ η′) σ PE.≡ wkₜ η (wkₜ η′ σ)
  wk-comp-comm {σ = σ} η η′ = PE.trans (PE.cong (λ x → U.wk x σ) (comp-eq η η′))
                                       (PE.sym (UP.wk-comp-comm (toWk η) (toWk η′) σ))

  comp-eq : ∀ {Γ Δ E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
          → toWk (η •ₜ η′) PE.≡ toWk η • toWk η′
  comp-eq base η′ = PE.refl
  comp-eq (step η) η′ = PE.cong step (comp-eq η η′)
  comp-eq (lift η) (step η′) = PE.cong step (comp-eq η η′)
  comp-eq (lift {Δ} {E} {.(wkₜ η′ σ)} η) (lift {Γ} {.Δ} {σ} η′) =
    HE.≅-to-≡
      (HE.trans
        (HE.cong₂ (λ X → toWk {Γ ∙ σ} {X})
                  (HE.≡-to-≅ (PE.cong (λ x → E ∙ x) (PE.sym (wk-comp-comm η η′))))
                  (subst-eq η η′))
        (HE.≡-to-≅ (PE.cong lift (comp-eq η η′))) )

  subst-eq : ∀ {Γ Δ E σ} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
           → HE._≅_ {A = Γ ∙ σ ⊆ E ∙ wkₜ η (wkₜ η′ σ)}
                    (PE.subst (λ x → Γ ∙ σ ⊆ E ∙ x) (wk-comp-comm η η′) (lift (η •ₜ η′)))
                    {B = Γ ∙ σ ⊆ E ∙ wkₜ (η •ₜ η′) σ}
                    (lift (η •ₜ η′))
  subst-eq η η′ = HE.≡-subst-removable (λ x → _ ∙ _ ⊆ _ ∙ x) (wk-comp-comm η η′) (lift (η •ₜ η′))

wk-comp-comm-lift : ∀ {Γ Δ E G} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
                  → wkLiftₜ (η •ₜ η′) G PE.≡ wkLiftₜ η (wkLiftₜ η′ G)
wk-comp-comm-lift {G = G} η η′ =
  PE.sym (PE.trans (UP.wk-comp-comm (lift (toWk η)) (lift (toWk η′)) G)
                   (PE.cong (λ x → U.wk (lift x) G) (PE.sym (comp-eq η η′))))

wk-comp-comm-subst : ∀ {Γ Δ E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) G
                   → wkLiftₜ (η •ₜ η′) G [ a ] PE.≡ wkLiftₜ η (wkLiftₜ η′ G) [ a ]
wk-comp-comm-subst {a = a} η η′ G = PE.cong (λ x → x [ a ]) (wk-comp-comm-lift {G = G} η η′)


-- Weakening of judgements

wkIndex : ∀ {Γ Δ x A} → (pr : Γ ⊆ Δ) →
        let A' = U.wk (toWk pr) A
            x' = wkNat (toWk pr) x
        in  ⊢ Δ → x ∷ A ∈ Γ → x' ∷ A' ∈ Δ
wkIndex base ⊢Δ ()
wkIndex (step pr) (⊢Δ ∙ x) i = PE.subst (λ x → _ ∷ x ∈ _)
                                        (wkIndex-step (toWk pr))
                                        (there (wkIndex pr ⊢Δ i))
wkIndex (lift pr) (⊢Δ ∙ x) (there i) = PE.subst (λ x → _ ∷ x ∈ _)
                                                (wkIndex-lift (toWk pr))
                                                (there (wkIndex pr ⊢Δ i))
wkIndex (lift pr) ⊢Δ here = PE.subst (let G = _; n = _ in λ x → n ∷ x ∈ G)
                                     (wkIndex-lift (toWk pr))
                                     here

mutual
  wk : ∀ {Γ Δ A} → (pr : Γ ⊆ Δ) →
     let A' = U.wk (toWk pr) A
     in  ⊢ Δ → Γ ⊢ A → Δ ⊢ A'
  wk pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wk pr ⊢Δ (U x) = U ⊢Δ
  wk pr ⊢Δ (Π A ▹ A₁) = let x = wk pr ⊢Δ A
                        in  Π x ▹ (wk (lift pr) (⊢Δ ∙ x) A₁)
  wk pr ⊢Δ (univ x) = univ (wkTerm pr ⊢Δ x)

  wkTerm : ∀ {Γ Δ A t} → (pr : Γ ⊆ Δ) →
         let Δ' = Δ
             A' = U.wk (toWk pr) A
             t' = U.wk (toWk pr) t
         in ⊢ Δ' → Γ ⊢ t ∷ A → Δ' ⊢ t' ∷ A'
  wkTerm pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wkTerm pr ⊢Δ (Π t ▹ t₁) = let x = wkTerm pr ⊢Δ t
                            in  Π x ▹ (wkTerm (lift pr) (⊢Δ ∙ univ x) t₁)
  wkTerm pr ⊢Δ (var x₁ x₂) = var ⊢Δ (wkIndex pr ⊢Δ x₂)
  wkTerm pr ⊢Δ (lam t t₁) = let x = wk pr ⊢Δ t
                            in lam x (wkTerm (lift pr) (⊢Δ ∙ x) t₁)
  wkTerm pr ⊢Δ (_∘_ {G = G} t t₁) = PE.subst (λ x → _ ⊢ _ ∷ x)
                                             (PE.sym (wk-β G))
                                             (wkTerm pr ⊢Δ t ∘ wkTerm pr ⊢Δ t₁)
  wkTerm pr ⊢Δ (zero x) = zero ⊢Δ
  wkTerm pr ⊢Δ (suc t) = suc (wkTerm pr ⊢Δ t)
  wkTerm {Δ = Δ} pr ⊢Δ (natrec {G = G} {s = s} x t t₁ t₂) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (natrec (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                     (PE.subst (λ x₁ → _ ⊢ _ ∷ x₁) (wk-β G) (wkTerm pr ⊢Δ t))
                     (PE.subst (λ x₁ → Δ ⊢ U.wk (toWk pr) s ∷ x₁) (wk-β-natrec (toWk pr) G) (wkTerm pr ⊢Δ t₁))
                     (wkTerm pr ⊢Δ t₂))
  wkTerm pr ⊢Δ (conv t₁ x) = conv (wkTerm pr ⊢Δ t₁) (wkEq pr ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
       let A' = U.wk (toWk pr) A
           B' = U.wk (toWk pr) B
       in ⊢ Δ → Γ ⊢ A ≡ B → Δ ⊢ A' ≡ B'
  wkEq pr ⊢Δ (univ x) = univ (wkEqTerm pr ⊢Δ x)
  wkEq pr ⊢Δ (refl x) = refl (wk pr ⊢Δ x)
  wkEq pr ⊢Δ (sym x) = sym (wkEq pr ⊢Δ x)
  wkEq pr ⊢Δ (trans x x₁) = trans (wkEq pr ⊢Δ x) (wkEq pr ⊢Δ x₁)
  wkEq pr ⊢Δ (Π-cong x x₁ x₂) = let y = wk pr ⊢Δ x
                                in  Π-cong y (wkEq pr ⊢Δ x₁) (wkEq (lift pr) (⊢Δ ∙ y) x₂)

  wkEqTerm : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ t' ≡ u' ∷ A'
  wkEqTerm pr ⊢Δ (refl x) = refl (wkTerm pr ⊢Δ x)
  wkEqTerm pr ⊢Δ (sym x) = sym (wkEqTerm pr ⊢Δ x)
  wkEqTerm pr ⊢Δ (trans x x₁) = trans (wkEqTerm pr ⊢Δ x) (wkEqTerm pr ⊢Δ x₁)
  wkEqTerm pr ⊢Δ (conv x x₁) = conv (wkEqTerm pr ⊢Δ x) (wkEq pr ⊢Δ x₁)
  wkEqTerm pr ⊢Δ (Π-cong x x₁ x₂) = let y = wk pr ⊢Δ x
                                    in  Π-cong y (wkEqTerm pr ⊢Δ x₁)
                                                 (wkEqTerm (lift pr) (⊢Δ ∙ y) x₂)
  wkEqTerm pr ⊢Δ (app-cong {G = G} x x₁) =
    PE.subst (λ x₂ → _ ⊢ _ ≡ _ ∷ x₂)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm pr ⊢Δ x) (wkEqTerm pr ⊢Δ x₁))
  wkEqTerm pr ⊢Δ (β-red {a = a} {b = b} {G = G} x x₁ x₂) =
    let y = wk pr ⊢Δ x
    in  PE.subst (λ x₂ → _ ⊢ _ ≡ _ ∷ x₂)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x₂ → _ ⊢ U.wk (toWk pr) ((lam b) ∘ a) ≡ x₂ ∷ _)
                           (PE.sym (wk-β b))
                           (β-red y (wkTerm (lift pr) (⊢Δ ∙ y) x₁) (wkTerm pr ⊢Δ x₂)))
  wkEqTerm pr ⊢Δ (fun-ext x x₁ x₂ x₃) =
    let y = wk pr ⊢Δ x
    in fun-ext y (wkTerm pr ⊢Δ x₁)
                 (wkTerm pr ⊢Δ x₂)
                 (PE.subst (λ t → _ ⊢ t ∘ _ ≡ _ ∷ _)
                           (PE.sym (wkIndex-lift (toWk pr)))
                           (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ∷ _)
                                     (PE.sym (wkIndex-lift (toWk pr)))
                                     (wkEqTerm (lift pr) (⊢Δ ∙ y) x₃)))
  wkEqTerm pr ⊢Δ (suc-cong x) = suc-cong (wkEqTerm pr ⊢Δ x)
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-cong {s = s} {s' = s'} {F = F} x x₁ x₂ x₃) =
    PE.subst (λ x₄ → Δ ⊢ natrec _ _ _ _ ≡ _ ∷ x₄) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
             (PE.subst (λ x₄ → Δ ⊢ _ ≡ _ ∷ x₄) (wk-β F) (wkEqTerm pr ⊢Δ x₁))
             (PE.subst (λ x₄ → Δ ⊢ U.wk (toWk pr) s ≡ U.wk (toWk pr) s' ∷ x₄) (wk-β-natrec (toWk pr) F) (wkEqTerm pr ⊢Δ x₂))
             (wkEqTerm pr ⊢Δ x₃))
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-zero {z} {s} {F} x x₁ x₂) =
    PE.subst (λ y → Δ ⊢ natrec (U.wk (lift (toWk pr)) F) _ _ _ ≡ _ ∷ y) (PE.sym (wk-β F))
             (natrec-zero (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                          (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) z ∷ y) (wk-β F) (wkTerm pr ⊢Δ x₁))
                          (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) s ∷ y) (wk-β-natrec (toWk pr) F) (wkTerm pr ⊢Δ x₂)))
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-suc {n} {z} {s} {F} x x₁ x₂ x₃) =
    PE.subst (λ y → Δ ⊢ natrec (U.wk (lift (toWk pr)) F) _ _ _ ≡ _ ∘ (natrec _ _ _ _) ∷ y) (PE.sym (wk-β F))
             (natrec-suc (wkTerm pr ⊢Δ x)
                         (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x₁)
                         (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) z ∷ y) (wk-β F) (wkTerm pr ⊢Δ x₂))
                         (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) s ∷ y) (wk-β-natrec (toWk pr) F) (wkTerm pr ⊢Δ x₃)))

mutual
  wkRed : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               B' = U.wk (toWk pr) B
           in ⊢ Δ → Γ ⊢ A ⇒ B → Δ ⊢ A' ⇒ B'
  wkRed pr ⊢Δ (univ x) = univ (wkRedTerm pr ⊢Δ x)

  wkRedTerm : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ t' ⇒ u' ∷ A'
  wkRedTerm pr ⊢Δ (conv r x) = conv (wkRedTerm pr ⊢Δ r) (wkEq pr ⊢Δ x)
  wkRedTerm pr ⊢Δ (app-subst {B = B} r x) =
    PE.subst (λ x₁ → _ ⊢ _ ⇒ _ ∷ x₁) (PE.sym (wk-β B))
             (app-subst (wkRedTerm pr ⊢Δ r) (wkTerm pr ⊢Δ x))
  wkRedTerm pr ⊢Δ (β-red {A} {B} {a} {t} x x₁ x₂) =
    PE.subst (λ x₃ → _ ⊢ _ ⇒ _ ∷ x₃) (PE.sym (wk-β B))
             ((PE.subst (λ x₂ → _ ⊢ U.wk (toWk pr) ((lam t) ∘ a) ⇒ x₂ ∷ _) (PE.sym (wk-β t))
                        (let y = wk pr ⊢Δ x
                         in  β-red y (wkTerm (lift pr) (⊢Δ ∙ y) x₁) (wkTerm pr ⊢Δ x₂))))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-subst {C} {g = g} x x₁ x₂ r) =
    PE.subst (λ x₃ → _ ⊢ natrec _ _ _ _ ⇒ _ ∷ x₃) (PE.sym (wk-β C))
             (natrec-subst (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                           (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                     (wkTerm pr ⊢Δ x₁))
                           (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃)
                                     (wk-β-natrec (toWk pr) C)
                                     (wkTerm pr ⊢Δ x₂))
                           (wkRedTerm pr ⊢Δ r))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-zero {C} {g = g} x x₁ x₂) =
    PE.subst (λ x₃ → _ ⊢ natrec (U.wk (lift (toWk pr)) C) _ _ _ ⇒ _ ∷ x₃) (PE.sym (wk-β C))
             (natrec-zero (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                          (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                    (wkTerm pr ⊢Δ x₁))
                          (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃) (wk-β-natrec (toWk pr) C)
                                    (wkTerm pr ⊢Δ x₂)))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-suc {C} {g = g} x x₁ x₂ x₃) =
    PE.subst (λ x₄ → _ ⊢ natrec _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ ∷ x₄) (PE.sym (wk-β C))
             (natrec-suc (wkTerm pr ⊢Δ x)
                         (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x₁)
                         (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                   (wkTerm pr ⊢Δ x₂))
                         (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃) (wk-β-natrec (toWk pr) C)
                                   (wkTerm pr ⊢Δ x₃)))

wkRed* : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               B' = U.wk (toWk pr) B
           in ⊢ Δ → Γ ⊢ A ⇒* B → Δ ⊢ A' ⇒* B'
wkRed* pr ⊢Δ (id A) = id (wk pr ⊢Δ A)
wkRed* pr ⊢Δ (x ⇨ r) = (wkRed pr ⊢Δ x) ⇨ (wkRed* pr ⊢Δ r)

wkRed*Term : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ t' ⇒* u' ∷ A'
wkRed*Term pr ⊢Δ (id t) = id (wkTerm pr ⊢Δ t)
wkRed*Term pr ⊢Δ (x ⇨ r) = (wkRedTerm pr ⊢Δ x) ⇨ (wkRed*Term pr ⊢Δ r)

wkRed:*: : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               B' = U.wk (toWk pr) B
           in ⊢ Δ → Γ ⊢ A :⇒*: B → Δ ⊢ A' :⇒*: B'
wkRed:*: pr ⊢Δ [ Γ⊢A , Γ⊢B , A⇒*B ] = [ wk pr ⊢Δ Γ⊢A , wk pr ⊢Δ Γ⊢B , wkRed* pr ⊢Δ A⇒*B ]

wkRed:*:Term : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A → Δ ⊢ t' :⇒*: u' ∷ A'
wkRed:*:Term pr ⊢Δ [ Γ⊢t , Γ⊢u , t⇒*u ] = [ wkTerm pr ⊢Δ Γ⊢t , wkTerm pr ⊢Δ Γ⊢u , wkRed*Term pr ⊢Δ t⇒*u ]
