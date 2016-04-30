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

cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {x y u v s t q r} → x ≡ y → u ≡ v → s ≡ t → q ≡ r
        → f x u s q ≡ f y v t r
cong₄ f refl refl refl refl = refl

iterate : {A : Set} → (A → A) → A → Nat → A
iterate s z zero = z
iterate s z (suc n) = s (iterate s z n)

arbLifts : (n : Nat) → Subst
arbLifts = iterate liftSubst idSubst

wkNat-id : (x : Nat) (n : Nat) → wkNat (iterate lift id n) x ≡ x
wkNat-id x zero = refl
wkNat-id zero (suc n) = refl
wkNat-id (suc x) (suc n) = cong suc (wkNat-id x n)

wk-id : (x : Term) (n : Nat) → wk (iterate lift id n) x ≡ x
wk-id U n = refl
wk-id (Π x ▹ x₁) n = cong₂ Π_▹_ (wk-id x n) (wk-id x₁ (suc n))
wk-id ℕ n = refl
wk-id (var x) n = cong var (wkNat-id x n)
wk-id (lam x) n = cong lam (wk-id x (suc n))
wk-id (x ∘ x₁) n = cong₂ _∘_ (wk-id x n) (wk-id x₁ n)
wk-id zero n = refl
wk-id (suc x) n = cong suc (wk-id x n)
wk-id (natrec x x₁ x₂ x₃) n = cong₄ natrec (wk-id x (suc n)) (wk-id x₁ n) (wk-id x₂ n) (wk-id x₃ n)

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
idSubst-lemma (natrec t t₁ t₂ t₃) n =
  cong₄ natrec (idSubst-lemma t (suc n)) (idSubst-lemma t₁ n) (idSubst-lemma t₂ n) (idSubst-lemma t₃ n)

idSubst-lemma₀ : (t : Term) → subst idSubst t ≡ t
idSubst-lemma₀ t = idSubst-lemma t zero

-- wellscoped-lemma-var : {Γ Δ : Con ⊤} (ρ : Γ ⊆ Δ) (x : Nat)
--                      → WellScoped.wkNat ρ x ≡ wkNat (toWk ρ) x
-- wellscoped-lemma-var base x = refl
-- wellscoped-lemma-var (step ρ) x = cong suc (wellscoped-lemma-var ρ x)
-- wellscoped-lemma-var (lift ρ) zero = refl
-- wellscoped-lemma-var (lift ρ) (suc x) = cong suc (wellscoped-lemma-var ρ x)

-- wellscoped-lemma : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) t → WellScoped.wk ρ t ≡ wk (toWk ρ) t
-- wellscoped-lemma ρ U = refl
-- wellscoped-lemma ρ (Π t ▹ t₁) = cong₂ Π_▹_ (wellscoped-lemma ρ t) (wellscoped-lemma (lift ρ) t₁)
-- wellscoped-lemma ρ ℕ = refl
-- wellscoped-lemma ρ (var x) = cong var (wellscoped-lemma-var ρ x)
-- wellscoped-lemma ρ (lam t) = cong lam (wellscoped-lemma (lift ρ) t)
-- wellscoped-lemma ρ (t ∘ t₁) = cong₂ _∘_ (wellscoped-lemma ρ t) (wellscoped-lemma ρ t₁)
-- wellscoped-lemma ρ zero = refl
-- wellscoped-lemma ρ (suc t) = cong suc (wellscoped-lemma ρ t)
-- wellscoped-lemma ρ (natrec t t₁ t₂) =
--   cong₃ natrec (wellscoped-lemma (lift ρ) t) (wellscoped-lemma ρ t₁) (wellscoped-lemma ρ t₂)

-- Composition properties

lift-step-comp : (p : Wk) → step id • p ≡ lift p • step id
lift-step-comp id = refl
lift-step-comp (step p) = cong step (lift-step-comp p)
lift-step-comp (lift p) = refl

wkNat-comp-comm : ∀ p q x → wkNat p (wkNat q x) ≡ wkNat (p • q) x
wkNat-comp-comm id q x = refl
wkNat-comp-comm (step p) q x = cong suc (wkNat-comp-comm p q x)
wkNat-comp-comm (lift p) id x = refl
wkNat-comp-comm (lift p) (step q) x = cong suc (wkNat-comp-comm p q x)
wkNat-comp-comm (lift p) (lift q) zero = refl
wkNat-comp-comm (lift p) (lift q) (suc x) = cong suc (wkNat-comp-comm p q x)

wk-comp-comm : ∀ p q t → wk p (wk q t) ≡ wk (p • q) t
wk-comp-comm p q U = refl
wk-comp-comm p q (Π t ▹ t₁) = cong₂ Π_▹_ (wk-comp-comm p q t) (wk-comp-comm (lift p) (lift q) t₁)
wk-comp-comm p q ℕ = refl
wk-comp-comm p q (var x) = cong var (wkNat-comp-comm p q x)
wk-comp-comm p q (lam t) = cong lam (wk-comp-comm (lift p) (lift q) t)
wk-comp-comm p q (t ∘ t₁) = cong₂ _∘_ (wk-comp-comm p q t) (wk-comp-comm p q t₁)
wk-comp-comm p q zero = refl
wk-comp-comm p q (suc t) = cong suc (wk-comp-comm p q t)
wk-comp-comm p q (natrec t t₁ t₂ t₃) = cong₄ natrec (wk-comp-comm (lift p) (lift q) t)
                                                    (wk-comp-comm p q t₁)
                                                    (wk-comp-comm p q t₂)
                                                    (wk-comp-comm p q t₃)

wkIndex-step : ∀ {A} pr → wk1 (wk pr A) ≡ wk (step pr) A
wkIndex-step pr = wk-comp-comm (step id) pr _

wkIndex-lift : ∀ {A} pr → wk1 (wk pr A) ≡ wk (lift pr) (wk (step id) A)
wkIndex-lift {A} pr = trans (wk-comp-comm (step id) pr A)
                            (trans (cong (λ x → wk x A) (lift-step-comp pr))
                                   (sym (wk-comp-comm (lift pr) (step id) A)))

postulate TODO : ∀ {a} {A : Set a} → A

subst-wk-var : ∀ {pr a} x n → wk (iterate lift pr n) (iterate liftSubst (unitSubst a) n x)
  ≡ iterate liftSubst (unitSubst (wk pr a)) n (wkNat (iterate lift (lift pr) n) x)
subst-wk-var zero zero = refl
subst-wk-var (suc x) zero = refl
subst-wk-var zero (suc n) = refl
subst-wk-var (suc x) (suc n) = TODO

subst-wk-dist : ∀ {pr a} t n → wk (iterate lift pr n) (subst (iterate liftSubst (unitSubst a) n) t)
  ≡ subst (iterate liftSubst (unitSubst (wk pr a)) n) (wk (iterate lift (lift pr) n) t)
subst-wk-dist U n = refl
subst-wk-dist (Π t ▹ t₁) n = cong₂ Π_▹_ (subst-wk-dist t n) (subst-wk-dist t₁ (suc n))
subst-wk-dist ℕ n = refl
subst-wk-dist (var x) n = subst-wk-var x n
subst-wk-dist (lam t) n = cong lam (subst-wk-dist t (suc n))
subst-wk-dist (t ∘ t₁) n = cong₂ _∘_ (subst-wk-dist t n) (subst-wk-dist t₁ n)
subst-wk-dist zero n = refl
subst-wk-dist (suc t) n = cong suc (subst-wk-dist t n)
subst-wk-dist (natrec t t₁ t₂ t₃) n = cong₄ natrec (subst-wk-dist t (suc n)) (subst-wk-dist t₁ n) (subst-wk-dist t₂ n) (subst-wk-dist t₃ n)

wk-β : ∀ {pr a} t → wk pr (t [ a ]) ≡ wk (lift pr) t [ wk pr a ]
wk-β t = subst-wk-dist t zero

wk-β-natrec : ∀ {pr} G →
      Π ℕ ▹
      (Π wk (lift pr) (G [ var zero ]) ▹
       wk (lift (lift pr)) (G [ suc (var (suc zero)) ]))
      ≡
      Π ℕ ▹
        (Π wk (lift pr) G [ var zero ] ▹
       (wk (lift pr) G [ suc (var (suc zero)) ]))
wk-β-natrec G = TODO
