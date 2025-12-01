{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Injection {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Union
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A t : Term n
    Γ : Con Term n

injl′ : ∀ {A B t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([B] : Γ ⊩⟨ l ⟩ B)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
       ([∪FG] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
     → Γ ⊩⟨ l′ ⟩ injl t ∷ A ∪ B / ∪-intr [∪FG]
injl′ {Γ = Γ} {A} {B} {t} {l} {l′} [A] [B] [t]
      [∪FG]@(noemb (∪ᵣ A₁ B₁ D ⊢A ⊢B A≡A [A]₁ [B]₁)) with
        ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  let ⊢t = escapeTerm [A] [t]
      ⊢Γ = wf ⊢A
      ⊢inj = injlⱼ ⊢B ⊢t
  in  ∪₁ₜ (injl t)
          (idRedTerm:*: ⊢inj)
          (≅-injl-cong ⊢B (escapeTermEq [A] (reflEqTerm [A] [t])))
          t
          injlₙ
          (irrelevanceTerm′ (PE.sym (wk-id A)) [A] ([A]₁ id ⊢Γ) [t])
injl′ {Γ = Γ} {A} {B} {t} {l} {l′} [B] [A] [t]
      [∪FG]@(emb 0<1 x) = injl′ [B] [A] [t] x

injr′ : ∀ {A B t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([B] : Γ ⊩⟨ l ⟩ B)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ B / [B])
       ([∪FG] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
     → Γ ⊩⟨ l′ ⟩ injr t ∷ A ∪ B / ∪-intr [∪FG]
injr′ {Γ = Γ} {A} {B} {t} {l} {l′} [A] [B] [t]
      [∪FG]@(noemb (∪ᵣ A₁ B₁ D ⊢A ⊢B A≡A [A]₁ [B]₁)) with
        ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  let ⊢t = escapeTerm [B] [t]
      ⊢Γ = wf ⊢B
      ⊢inj = injrⱼ ⊢A ⊢t
  in  ∪₂ₜ (injr t)
          (idRedTerm:*: ⊢inj)
          (≅-injr-cong ⊢A (escapeTermEq [B] (reflEqTerm [B] [t])))
          t
          injrₙ
          (irrelevanceTerm′ (PE.sym (wk-id B)) [B] ([B]₁ id ⊢Γ) [t])
injr′ {Γ = Γ} {A} {B} {t} {l} {l′} [B] [A] [t]
      [∪FG]@(emb 0<1 x) = injr′ [B] [A] [t] x

injl″ : ∀ {A B t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([B] : Γ ⊩⟨ l ⟩ B)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
       ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
     → Γ ⊩⟨ l′ ⟩ injl t ∷ A ∪ B / [∪AB]
injl″ [A] [B] [t] [∪AB] =
  irrelevanceTerm (∪-intr (∪-elim [∪AB])) [∪AB] (injl′ [A] [B] [t] (∪-elim [∪AB]))

injr″ : ∀ {A B t l l′}
       ([A] : Γ ⊩⟨ l ⟩ A)
       ([B] : Γ ⊩⟨ l ⟩ B)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ B / [B])
       ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
     → Γ ⊩⟨ l′ ⟩ injr t ∷ A ∪ B / [∪AB]
injr″ [A] [B] [t] [∪AB] =
  irrelevanceTerm (∪-intr (∪-elim [∪AB])) [∪AB] (injr′ [A] [B] [t] (∪-elim [∪AB]))

injl-cong′ : ∀ {A B t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([B] : Γ ⊩⟨ l ⟩ B)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ A / [A])
             ([t≡u] : Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A])
             ([∪AB] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
             → Γ ⊩⟨ l′ ⟩ injl t ≡ injl u ∷ A ∪ B / ∪-intr [∪AB]
injl-cong′ {Γ = Γ} {A} {B} {t} {u} {l} {l′}
           [A] [B] [t] [u] [t≡u]
           [∪AB]@(noemb (∪ᵣ A₁ B₁ D ⊢F ⊢G A≡A [A]₁ [B]₁)) with
             ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  let [inj]   = injl′ [A] [B] [t] [∪AB]
      [inj']  = injl′ [A] [B] [u] [∪AB]
      ⊢Γ      = wf ⊢F
      wk[A]   = [A]₁ id ⊢Γ
      wk[t≡u] = irrelevanceEqTerm′ (PE.sym (wk-id A)) [A] wk[A] [t≡u]
      ⊢inj    = escapeTerm (∪-intr [∪AB]) [inj]
      ⊢inj′   = escapeTerm (∪-intr [∪AB]) [inj']
  in ∪₁ₜ₌ (injl t) (injl u) (idRedTerm:*: ⊢inj) (idRedTerm:*: ⊢inj′)
          (≅-injl-cong ⊢G (escapeTermEq [A] [t≡u]))
          [inj] [inj'] t u injlₙ injlₙ wk[t≡u]
injl-cong′ [A] [B] [t] [u] [t≡u] (emb 0<1 x) =
  injl-cong′ [A] [B] [t] [u] [t≡u] x

injr-cong′ : ∀ {A B t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([B] : Γ ⊩⟨ l ⟩ B)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ B / [B])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ B / [B])
             ([t≡u] : Γ ⊩⟨ l ⟩ t ≡ u ∷ B / [B])
             ([∪AB] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
             → Γ ⊩⟨ l′ ⟩ injr t ≡ injr u ∷ A ∪ B / ∪-intr [∪AB]
injr-cong′ {Γ = Γ} {A} {B} {t} {u} {l} {l′}
           [A] [B] [t] [u] [t≡u]
           [∪AB]@(noemb (∪ᵣ A₁ B₁ D ⊢F ⊢G A≡A [A]₁ [B]₁)) with
             ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  let [inj]   = injr′ [A] [B] [t] [∪AB]
      [inj']  = injr′ [A] [B] [u] [∪AB]
      ⊢Γ      = wf ⊢G
      wk[B]   = [B]₁ id ⊢Γ
      wk[t≡u] = irrelevanceEqTerm′ (PE.sym (wk-id B)) [B] wk[B] [t≡u]
      ⊢inj    = escapeTerm (∪-intr [∪AB]) [inj]
      ⊢inj′   = escapeTerm (∪-intr [∪AB]) [inj']
  in ∪₂ₜ₌ (injr t) (injr u) (idRedTerm:*: ⊢inj) (idRedTerm:*: ⊢inj′)
          (≅-injr-cong ⊢F (escapeTermEq [B] [t≡u]))
          [inj] [inj'] t u injrₙ injrₙ wk[t≡u]
injr-cong′ [A] [B] [t] [u] [t≡u] (emb 0<1 x) =
  injr-cong′ [A] [B] [t] [u] [t≡u] x

injl-cong″ : ∀ {A B t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([B] : Γ ⊩⟨ l ⟩ B)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ A / [A])
             ([t≡u′] : Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A])
             ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
             → Γ ⊩⟨ l′ ⟩ injl t ≡ injl u ∷ A ∪ B / [∪AB]
injl-cong″ [A] [B] [t] [u] [t≡u] [∪AB] =
  let [inj≡] = injl-cong′ [A] [B] [t] [u] [t≡u] (∪-elim [∪AB])
  in  irrelevanceEqTerm (∪-intr (∪-elim [∪AB])) [∪AB] [inj≡]

injr-cong″ : ∀ {A B t u l l′}
             ([A] : Γ ⊩⟨ l ⟩ A)
             ([B] : Γ ⊩⟨ l ⟩ B)
             ([t] : Γ ⊩⟨ l ⟩ t ∷ B / [B])
             ([u] : Γ ⊩⟨ l ⟩ u ∷ B / [B])
             ([t≡u′] : Γ ⊩⟨ l ⟩ t ≡ u ∷ B / [B])
             ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
             → Γ ⊩⟨ l′ ⟩ injr t ≡ injr u ∷ A ∪ B / [∪AB]
injr-cong″ [A] [B] [t] [u] [t≡u] [∪AB] =
  let [inj≡] = injr-cong′ [A] [B] [t] [u] [t≡u] (∪-elim [∪AB])
  in  irrelevanceEqTerm (∪-intr (∪-elim [∪AB])) [∪AB] [inj≡]

injl-congᵛ : ∀ {A B t u l}
             ([Γ] : ⊩ᵛ Γ)
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
             ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
             ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A])
             ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A])
             → Γ ⊩ᵛ⟨ l ⟩ injl t ≡ injl u ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B]
injl-congᵛ {Γ = Γ} {A} {B} {t} {u} [Γ] [A] [B] [t] [u] [t≡u] {Δ = Δ} {σ} ⊢Δ [σ] =
  let ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σB   = proj₁ ([B] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σu   = proj₁ ([u] ⊢Δ [σ])
      σt≡σu = [t≡u] ⊢Δ [σ]
      ⊩σ∪AB = proj₁ (∪ᵛ {F = A} {B} [Γ] [A] [B] ⊢Δ [σ])
  in injl-cong″ ⊩σA ⊩σB ⊩σt ⊩σu σt≡σu ⊩σ∪AB

injr-congᵛ : ∀ {A B t u l}
             ([Γ] : ⊩ᵛ Γ)
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
             ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B])
             ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ B / [Γ] / [B])
             ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B / [Γ] / [B])
             → Γ ⊩ᵛ⟨ l ⟩ injr t ≡ injr u ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B]
injr-congᵛ {Γ = Γ} {A} {B} {t} {u} [Γ] [A] [B] [t] [u] [t≡u] {Δ = Δ} {σ} ⊢Δ [σ] =
  let ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σB   = proj₁ ([B] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σu   = proj₁ ([u] ⊢Δ [σ])
      σt≡σu = [t≡u] ⊢Δ [σ]
      ⊩σ∪AB = proj₁ (∪ᵛ {F = A} {B} [Γ] [A] [B] ⊢Δ [σ])
  in injr-cong″ ⊩σA ⊩σB ⊩σt ⊩σu σt≡σu ⊩σ∪AB

injlᵛ : ∀ {A B t l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
       ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
     → Γ ⊩ᵛ⟨ l ⟩ injl t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B]
injlᵛ {Γ = Γ} {A} {B} {t} {l} [Γ] [A] [B] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB] = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σB   = proj₁ ([B] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σ∪AB = proj₁ ([∪AB] ⊢Δ [σ])

  in  injl″ ⊩σA ⊩σB ⊩σt ⊩σ∪AB ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let ⊩σ′A   = proj₁ ([A] ⊢Δ [σ′])
            σA≡σ′A = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
            ⊩σ′t   = convTerm₂ ⊩σA ⊩σ′A σA≡σ′A (proj₁ ([t] ⊢Δ [σ′]))
            σt≡σ′t = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  injl-cong″ ⊩σA ⊩σB ⊩σt ⊩σ′t σt≡σ′t ⊩σ∪AB)

injrᵛ : ∀ {A B t l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
       ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B])
     → Γ ⊩ᵛ⟨ l ⟩ injr t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B]
injrᵛ {Γ = Γ} {A} {B} {t} {l} [Γ] [A] [B] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB] = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      ⊩σA   = proj₁ ([A] ⊢Δ [σ])
      ⊩σB   = proj₁ ([B] ⊢Δ [σ])
      ⊩σt   = proj₁ ([t] ⊢Δ [σ])
      ⊩σ∪AB = proj₁ ([∪AB] ⊢Δ [σ])

  in  injr″ ⊩σA ⊩σB ⊩σt ⊩σ∪AB ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let ⊩σ′B   = proj₁ ([B] ⊢Δ [σ′])
            σB≡σ′B = proj₂ ([B] ⊢Δ [σ]) [σ′] [σ≡σ′]
            ⊩σ′t   = convTerm₂ ⊩σB ⊩σ′B σB≡σ′B (proj₁ ([t] ⊢Δ [σ′]))
            σt≡σ′t = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  injr-cong″ ⊩σA ⊩σB ⊩σt ⊩σ′t σt≡σ′t ⊩σ∪AB)
