module Definition.Untyped.Indexed where

open import Data.Unit
open import Data.Product
open import Tools.Context as Context
open Context.NonDependent

data Term (Γ : Con ⊤) : Set where
  U : Term Γ
  Π_▹_ : Term Γ → Term (Γ ∙ tt) → Term Γ
  ℕ : Term Γ
  var : tt ∈ Γ → Term Γ
  lam : Term (Γ ∙ tt) → Term Γ
  _∘_ : Term Γ → Term Γ → Term Γ
  zero : Term Γ
  suc : Term Γ → Term Γ
  natrec : Term (Γ ∙ tt) → Term Γ → Term Γ → Term Γ → Term Γ

wk : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (t : Term Γ) → Term Δ
wk ρ U = U
wk ρ (Π t ▹ t₁) = Π wk ρ t ▹ wk (lift ρ) t₁
wk ρ ℕ = ℕ
wk ρ (var x) = var (weak ρ x)
wk ρ (lam t) = lam (wk (lift ρ) t)
wk ρ (t ∘ t₁) = (wk ρ t) ∘ (wk ρ t₁)
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec t t₁ t₂ t₃) = natrec (wk (lift ρ) t) (wk ρ t₁) (wk ρ t₂) (wk ρ t₃)

wk1 : ∀ {Γ} → Term Γ → Term (Γ ∙ tt)
wk1 = wk (step (⊆-refl _))

Subst : Con ⊤ → Con ⊤ → Set
Subst Δ ε = ⊤
Subst Δ (Γ ∙ γ) = Term Δ × Subst Δ Γ

substVar : ∀ {Γ Δ} (σ : Subst Δ Γ) (x : tt ∈ Γ) → Term Δ
substVar (proj₁ , proj₂) here = proj₁
substVar (proj₁ , proj₂) (there x) = substVar proj₂ x

wk1Subst : ∀ {Γ} Δ → Subst Γ Δ → Subst (Γ ∙ tt) Δ
wk1Subst ε x = tt
wk1Subst (Δ ∙ x) (proj₁ , proj₂) = wk1 proj₁ , wk1Subst Δ proj₂

idSubst : ∀ Γ → Subst Γ Γ
idSubst ε = tt
idSubst (Γ ∙ x) = var here , wk1Subst Γ (idSubst Γ)

liftSubst : ∀ {Γ Δ} → (σ : Subst Δ Γ) → Subst (Δ ∙ tt) (Γ ∙ tt)
liftSubst σ = var here , wk1Subst _ σ

subst : ∀ {Γ Δ} (σ : Subst Δ Γ) (t : Term Γ) → Term Δ
subst σ U = U
subst σ (Π t ▹ t₁) = Π subst σ t ▹ subst (liftSubst σ) t₁
subst σ ℕ = ℕ
subst σ (var x) = substVar σ x
subst σ (lam t) = lam (subst (liftSubst σ) t)
subst σ (t ∘ t₁) = (subst σ t) ∘ (subst σ t₁)
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (natrec t t₁ t₂ t₃) = natrec (subst (liftSubst σ) t) (subst σ t₁) (subst σ t₂) (subst σ t₃)

_[_] : ∀ {Γ} (t : Term (Γ ∙ tt)) (s : Term Γ) → Term Γ
t [ s ] = subst (s , idSubst _) t
