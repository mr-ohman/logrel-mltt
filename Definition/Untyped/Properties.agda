module Definition.Untyped.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Definition.Untyped
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Tools.Context
open import Data.Unit

subst-test₁ : {x : Term} → lam (var 0) [ x ] ≡ lam (var 0)
subst-test₁ = refl

subst-test₂ : {x : Term} → lam (var 1) [ x ] ≡ lam (wk1 x)
subst-test₂ = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b
        → f x u a ≡ f y v b
cong₃ f refl refl refl = refl

arbLifts : (n : Nat) → Subst
arbLifts zero = idSubst
arbLifts (suc n) = liftSubst (arbLifts n)

idSubst-lemma-var : (m n : Nat) → substVar (arbLifts n) m ≡ var m
idSubst-lemma-var m zero = refl
idSubst-lemma-var zero (suc n) = refl
idSubst-lemma-var (suc m) (suc n) = cong (wk (step id)) (idSubst-lemma-var m n)

idSubst-lemma : (t : Term) (n : Nat) → subst (arbLifts n) t ≡ t
idSubst-lemma U n = refl
idSubst-lemma (Π t ▹ t₁) n = cong₂ Π_▹_ (idSubst-lemma t n) (idSubst-lemma t₁ (suc n))
idSubst-lemma ℕ n = refl
idSubst-lemma (var x) n = idSubst-lemma-var x n
idSubst-lemma (lam t) n = cong lam (idSubst-lemma t (suc n))
idSubst-lemma (t ∘ t₁) n = cong₂ _∘_ (idSubst-lemma t n) (idSubst-lemma t₁ n)
idSubst-lemma zero n = refl
idSubst-lemma (suc t) n = cong suc (idSubst-lemma t n)
idSubst-lemma (natrec t t₁ t₂) n =
  cong₃ natrec (idSubst-lemma t (suc n)) (idSubst-lemma t₁ n) (idSubst-lemma t₂ n)

idSubst-lemma₀ : (t : Term) → subst idSubst t ≡ t
idSubst-lemma₀ t = idSubst-lemma t zero

wellscoped-lemma-var : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (x : Nat)
                     → WellScoped.wkNat ρ x ≡ wkNat (toWk ρ) x
wellscoped-lemma-var base x = refl
wellscoped-lemma-var (step ρ) x = cong suc (wellscoped-lemma-var ρ x)
wellscoped-lemma-var (lift ρ) zero = refl
wellscoped-lemma-var (lift ρ) (suc x) = cong suc (wellscoped-lemma-var ρ x)

wellscoped-lemma : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) t → WellScoped.wk ρ t ≡ wk (toWk ρ) t
wellscoped-lemma ρ U = refl
wellscoped-lemma ρ (Π t ▹ t₁) = cong₂ Π_▹_ (wellscoped-lemma ρ t) (wellscoped-lemma (lift ρ) t₁)
wellscoped-lemma ρ ℕ = refl
wellscoped-lemma ρ (var x) = cong var (wellscoped-lemma-var ρ x)
wellscoped-lemma ρ (lam t) = cong lam (wellscoped-lemma (lift ρ) t)
wellscoped-lemma ρ (t ∘ t₁) = cong₂ _∘_ (wellscoped-lemma ρ t) (wellscoped-lemma ρ t₁)
wellscoped-lemma ρ zero = refl
wellscoped-lemma ρ (suc t) = cong suc (wellscoped-lemma ρ t)
wellscoped-lemma ρ (natrec t t₁ t₂) =
  cong₃ natrec (wellscoped-lemma (lift ρ) t) (wellscoped-lemma ρ t₁) (wellscoped-lemma ρ t₂)
