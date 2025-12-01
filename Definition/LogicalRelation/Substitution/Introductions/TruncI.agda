{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.TruncI {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Trunc
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A t : Term n
    Γ : Con Term n

∥ᵢ′ : ∀ {A t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
       ([∥F∥] : Γ ⊩⟨ l′ ⟩∥ ∥ A ∥)
     → Γ ⊩⟨ l′ ⟩ ∥ᵢ t ∷ ∥ A ∥ / ∥-intr [∥F∥]
∥ᵢ′ {Γ = Γ} {A} {t} {l} {l′} [A] [t]
      [∥F∥]@(noemb (∥ᵣ A₁ D ⊢A A≡A [A]₁)) with
        ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
... | PE.refl =
  let ⊢t = escapeTerm [A] [t]
      ⊢Γ = wf ⊢A
      ⊢inj = ∥ᵢⱼ ⊢t
  in  ∥₁ₜ (∥ᵢ t)
          (idRedTerm:*: ⊢inj)
          (≅-∥ᵢ-cong ⊢A (escapeTermEq [A] (reflEqTerm [A] [t])))
          t
          ∥ᵢₙ
          (irrelevanceTerm′ (PE.sym (wk-id A)) [A] ([A]₁ id ⊢Γ) [t])
∥ᵢ′ {Γ = Γ} {A} {t} {l} {l′} [A] [t]
      [∥F∥]@(emb 0<1 x) = ∥ᵢ′ [A] [t] x

∥ᵢ″ : ∀ {A t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
       ([∥A∥] : Γ ⊩⟨ l′ ⟩ ∥ A ∥)
     → Γ ⊩⟨ l′ ⟩ ∥ᵢ t ∷ ∥ A ∥ / [∥A∥]
∥ᵢ″ [A] [t] [∥A∥] =
  irrelevanceTerm (∥-intr (∥-elim [∥A∥])) [∥A∥] (∥ᵢ′ [A] [t] (∥-elim [∥A∥]))

∥ᵢ-cong′ : ∀ {A t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ A / [A])
             ([t≡u] : Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A])
             ([∥A∥] : Γ ⊩⟨ l′ ⟩∥ ∥ A ∥)
             → Γ ⊩⟨ l′ ⟩ ∥ᵢ t ≡ ∥ᵢ u ∷ ∥ A ∥ / ∥-intr [∥A∥]
∥ᵢ-cong′ {Γ = Γ} {A} {t} {u} {l} {l′}
           [A] [t] [u] [t≡u]
           [∥A∥]@(noemb (∥ᵣ A₁ D ⊢F A≡A [A]₁)) with
             ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
... | PE.refl =
  let [i]     = ∥ᵢ′ [A] [t] [∥A∥]
      [i']    = ∥ᵢ′ [A] [u] [∥A∥]
      ⊢Γ      = wf ⊢F
      wk[A]   = [A]₁ id ⊢Γ
      wk[t≡u] = irrelevanceEqTerm′ (PE.sym (wk-id A)) [A] wk[A] [t≡u]
      ⊢i      = escapeTerm (∥-intr [∥A∥]) [i]
      ⊢i′     = escapeTerm (∥-intr [∥A∥]) [i']
  in ∥₁ₜ₌ (∥ᵢ t) (∥ᵢ u) (idRedTerm:*: ⊢i) (idRedTerm:*: ⊢i′)
          (≅-∥ᵢ-cong ⊢F (escapeTermEq [A] [t≡u]))
          [i] [i'] t u ∥ᵢₙ ∥ᵢₙ wk[t≡u]
∥ᵢ-cong′ [A] [t] [u] [t≡u] (emb 0<1 x) =
  ∥ᵢ-cong′ [A] [t] [u] [t≡u] x

∥ᵢ-cong″ : ∀ {A t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ A / [A])
             ([t≡u′] : Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A])
             ([∥A∥] : Γ ⊩⟨ l′ ⟩ ∥ A ∥)
             → Γ ⊩⟨ l′ ⟩ ∥ᵢ t ≡ ∥ᵢ u ∷ ∥ A ∥ / [∥A∥]
∥ᵢ-cong″ [A] [t] [u] [t≡u] [∥A∥] =
  let [i≡] = ∥ᵢ-cong′ [A] [t] [u] [t≡u] (∥-elim [∥A∥])
  in  irrelevanceEqTerm (∥-intr (∥-elim [∥A∥])) [∥A∥] [i≡]

∥ᵢ-congᵛ : ∀ {A t u l}
             ([Γ] : ⊩ᵛ Γ)
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
             ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A])
             ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A])
             → Γ ⊩ᵛ⟨ l ⟩ ∥ᵢ t ≡ ∥ᵢ u ∷ ∥ A ∥ / [Γ] / ∥ᵛ {F = A} [Γ] [A]
∥ᵢ-congᵛ {Γ = Γ} {A} {t} {u} [Γ] [A] [t] [u] [t≡u] {Δ = Δ} {σ} ⊢Δ [σ] =
  let ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σu   = proj₁ ([u] ⊢Δ [σ])
      σt≡σu = [t≡u] ⊢Δ [σ]
      ⊩σ∥A∥ = proj₁ (∥ᵛ {F = A} [Γ] [A] ⊢Δ [σ])
  in ∥ᵢ-cong″ ⊩σA ⊩σt ⊩σu σt≡σu ⊩σ∥A∥

∥ᵢᵛ : ∀ {A t l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
     → Γ ⊩ᵛ⟨ l ⟩ ∥ᵢ t ∷ ∥ A ∥ / [Γ] / ∥ᵛ {F = A} [Γ] [A]
∥ᵢᵛ {Γ = Γ} {A} {t} {l} [Γ] [A] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∥A∥] = ∥ᵛ {F = A} [Γ] [A]
      ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σ∥A∥ = proj₁ ([∥A∥] ⊢Δ [σ])

  in  ∥ᵢ″ ⊩σA ⊩σt ⊩σ∥A∥ ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let ⊩σ′A   = proj₁ ([A] ⊢Δ [σ′])
            σA≡σ′A = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
            ⊩σ′t   = convTerm₂ ⊩σA ⊩σ′A σA≡σ′A (proj₁ ([t] ⊢Δ [σ′]))
            σt≡σ′t = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  ∥ᵢ-cong″ ⊩σA ⊩σt ⊩σ′t σt≡σ′t ⊩σ∥A∥)
