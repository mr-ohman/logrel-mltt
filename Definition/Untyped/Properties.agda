module Definition.Untyped.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Definition.Untyped
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality as PE hiding ([_]; subst)
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

-- wk-lift-id : ∀ t → wk (lift id) t ≡ wk id t
-- wk-lift-id t = {!!}

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

-- Context subset properties

-- mutual
--   ⊆-refl : (Γ : Con Term) → Γ ⊆ Γ
--   ⊆-refl ε = base
--   ⊆-refl (Γ ∙ x) = PE.subst (λ x₁ → Γ ∙ x ⊆ Γ ∙ x₁) (wk-⊆-refl Γ x) (lift (⊆-refl Γ))

--   wk-⊆-refl-lift : ∀ Γ t → wk (lift (toWk (⊆-refl Γ))) t ≡ wk (toWk (⊆-refl Γ)) t
--   wk-⊆-refl-lift ε t = wk-lift-id t
--   wk-⊆-refl-lift (Γ ∙ x) t = {!!}

--   wk-⊆-refl : ∀ Γ t → wk (toWk (⊆-refl Γ)) t ≡ t
--   wk-⊆-refl Γ U = refl
--   wk-⊆-refl Γ (Π t ▹ t₁) = {!!}
--   wk-⊆-refl Γ ℕ = refl
--   wk-⊆-refl Γ (var x) = {!!}
--   wk-⊆-refl Γ (lam t) = cong lam (trans (wk-⊆-refl-lift Γ t) (wk-⊆-refl Γ t))
--   wk-⊆-refl Γ (t ∘ t₁) = {!!}
--   wk-⊆-refl Γ zero = refl
--   wk-⊆-refl Γ (suc t) = {!!}
--   wk-⊆-refl Γ (natrec t t₁ t₂ t₃) = {!!}

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

wkIndex-lift : ∀ {A} pr → wk1 (wk pr A) ≡ wk (lift pr) (wk1 A)
wkIndex-lift {A} pr = trans (wk-comp-comm (step id) pr A)
                            (trans (cong (λ x → wk x A) (lift-step-comp pr))
                                   (sym (wk-comp-comm (lift pr) (step id) A)))



-- Weakening and substitution

substVar-liftSubst : ∀ {ρ ρ'} → (∀ m → substVar ρ m ≡ substVar ρ' m)
      → (n : Nat) → substVar (liftSubst ρ) n ≡ substVar (liftSubst ρ') n
substVar-liftSubst prf zero = refl
substVar-liftSubst prf (suc n) = cong wk1 (prf n)

subst-liftSubst : ∀ {ρ ρ'} t → (∀ n → ρ n ≡ ρ' n) → subst (liftSubst ρ) t ≡ subst (liftSubst ρ') t
subst-liftSubst U prf = refl
subst-liftSubst (Π t ▹ t₁) prf = cong₂ Π_▹_ (subst-liftSubst t prf) (subst-liftSubst t₁ (substVar-liftSubst prf))
subst-liftSubst ℕ prf = refl
subst-liftSubst (var x) prf = substVar-liftSubst prf x
subst-liftSubst (lam t) prf = cong lam (subst-liftSubst t (substVar-liftSubst prf))
subst-liftSubst (t ∘ t₁) prf = cong₂ _∘_ (subst-liftSubst t prf) (subst-liftSubst t₁ prf)
subst-liftSubst zero prf = refl
subst-liftSubst (suc t) prf = cong suc (subst-liftSubst t prf)
subst-liftSubst (natrec t t₁ t₂ t₃) prf = cong₄ natrec (subst-liftSubst t (substVar-liftSubst prf)) (subst-liftSubst t₁ prf) (subst-liftSubst t₂ prf) (subst-liftSubst t₃ prf)

substVar-wkSubst-liftSubst : ∀ {pr ρ} n → substVar (wkSubst (lift pr) (liftSubst ρ)) n ≡ substVar (liftSubst (wkSubst pr ρ)) n
substVar-wkSubst-liftSubst zero = refl
substVar-wkSubst-liftSubst (suc n) = sym (wkIndex-lift _)

wkSubst-liftSubst : ∀ {pr ρ} t → subst (wkSubst (lift pr) (liftSubst ρ)) t ≡
      subst (liftSubst (wkSubst pr ρ)) t
wkSubst-liftSubst U = refl
wkSubst-liftSubst (Π t ▹ t₁) = cong₂ Π_▹_ (wkSubst-liftSubst t) ((subst-liftSubst t₁ substVar-wkSubst-liftSubst))
wkSubst-liftSubst ℕ = refl
wkSubst-liftSubst (var x) = substVar-wkSubst-liftSubst x
wkSubst-liftSubst (lam t) = cong lam (subst-liftSubst t substVar-wkSubst-liftSubst)
wkSubst-liftSubst (t ∘ t₁) = cong₂ _∘_ (wkSubst-liftSubst t) (wkSubst-liftSubst t₁)
wkSubst-liftSubst zero = refl
wkSubst-liftSubst (suc t) = cong suc (wkSubst-liftSubst t)
wkSubst-liftSubst (natrec t t₁ t₂ t₃) = cong₄ natrec (subst-liftSubst t substVar-wkSubst-liftSubst) (wkSubst-liftSubst t₁) (wkSubst-liftSubst t₂) (wkSubst-liftSubst t₃)

substVar-purge-liftSubst : ∀ {pr ρ} (n : Nat) →
      substVar (purge (lift pr) (liftSubst ρ)) n ≡ substVar (liftSubst (purge pr ρ)) n
substVar-purge-liftSubst zero = refl
substVar-purge-liftSubst (suc n) = refl

purge-liftSubst : ∀ {pr ρ} t → subst (purge (lift pr) (liftSubst ρ)) t ≡
      subst (liftSubst (purge pr ρ)) t
purge-liftSubst U = refl
purge-liftSubst (Π t ▹ t₁) = cong₂ Π_▹_ (purge-liftSubst t) (subst-liftSubst t₁ substVar-purge-liftSubst)
purge-liftSubst ℕ = refl
purge-liftSubst (var x) = substVar-purge-liftSubst x
purge-liftSubst (lam t) = cong lam (subst-liftSubst t substVar-purge-liftSubst)
purge-liftSubst (t ∘ t₁) = cong₂ _∘_ (purge-liftSubst t) (purge-liftSubst t₁)
purge-liftSubst zero = refl
purge-liftSubst (suc t) = cong suc (purge-liftSubst t)
purge-liftSubst (natrec t t₁ t₂ t₃) = cong₄ natrec (subst-liftSubst t substVar-purge-liftSubst) (purge-liftSubst t₁) (purge-liftSubst t₂) (purge-liftSubst t₃)

wk-subst : ∀ {pr ρ} t → wk pr (subst ρ t) ≡ subst (wkSubst pr ρ) t
wk-subst U = refl
wk-subst (Π t ▹ t₁) = cong₂ Π_▹_ (wk-subst t) (trans (wk-subst t₁) (wkSubst-liftSubst t₁))
wk-subst ℕ = refl
wk-subst (var x) = refl
wk-subst (lam t) = cong lam (trans (wk-subst t) (wkSubst-liftSubst t))
wk-subst (t ∘ t₁) = cong₂ _∘_ (wk-subst t) (wk-subst t₁)
wk-subst zero = refl
wk-subst (suc t) = cong suc (wk-subst t)
wk-subst (natrec t t₁ t₂ t₃) = cong₄ natrec (trans (wk-subst t) (wkSubst-liftSubst t)) (wk-subst t₁) (wk-subst t₂) (wk-subst t₃)

subst-wk : ∀ {pr ρ} t → subst ρ (wk pr t) ≡ subst (purge pr ρ) t
subst-wk U = refl
subst-wk (Π t ▹ t₁) = cong₂ Π_▹_ (subst-wk t) (trans (subst-wk t₁) (purge-liftSubst t₁))
subst-wk ℕ = refl
subst-wk (var x) = refl
subst-wk (lam t) = cong lam (trans (subst-wk t) (purge-liftSubst t))
subst-wk (t ∘ t₁) = cong₂ _∘_ (subst-wk t) (subst-wk t₁)
subst-wk zero = refl
subst-wk (suc t) = cong suc (subst-wk t)
subst-wk (natrec t t₁ t₂ t₃) = cong₄ natrec (trans (subst-wk t) (purge-liftSubst t)) (subst-wk t₁) (subst-wk t₂) (subst-wk t₃)

-- Beta reduction weakening

substVar-wk-β-lemma : ∀ {pr a} (n : Nat) →
      purge (lift pr) (consSubst idSubst (wk pr a)) n ≡
      wkSubst pr (consSubst idSubst a) n
substVar-wk-β-lemma zero = refl
substVar-wk-β-lemma (suc n) = refl

wk-β-lemma : ∀ {pr a} t → subst (purge (lift pr) (consSubst idSubst (wk pr a))) t ≡
      subst (wkSubst pr (consSubst idSubst a)) t
wk-β-lemma U = refl
wk-β-lemma (Π t ▹ t₁) = cong₂ Π_▹_ (wk-β-lemma t) (subst-liftSubst t₁ substVar-wk-β-lemma)
wk-β-lemma ℕ = refl
wk-β-lemma (var x) = substVar-wk-β-lemma x
wk-β-lemma (lam t) = cong lam (subst-liftSubst t substVar-wk-β-lemma)
wk-β-lemma (t ∘ t₁) = cong₂ _∘_ (wk-β-lemma t) (wk-β-lemma t₁)
wk-β-lemma zero = refl
wk-β-lemma (suc t) = cong suc (wk-β-lemma t)
wk-β-lemma (natrec t t₁ t₂ t₃) = cong₄ natrec (subst-liftSubst t substVar-wk-β-lemma) (wk-β-lemma t₁) (wk-β-lemma t₂) (wk-β-lemma t₃)

wk-β : ∀ {pr a} t → wk pr (t [ a ]) ≡ wk (lift pr) t [ wk pr a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t) (wk-β-lemma t)))

substVar-wk-β-lemma↑ : ∀ {pr a} (n : Nat) →
      purge (lift pr) (consSubst (wk1Subst idSubst) (wk (lift pr) a)) n ≡
      wkSubst (lift pr) (consSubst (wk1Subst idSubst) a) n
substVar-wk-β-lemma↑ zero = refl
substVar-wk-β-lemma↑ (suc n) = refl

wk-β-lemma↑ : ∀ {pr a} t → subst (purge (lift pr) (consSubst (wk1Subst idSubst) (wk (lift pr) a)))
      t
      ≡ subst (wkSubst (lift pr) (consSubst (wk1Subst idSubst) a)) t
wk-β-lemma↑ U = refl
wk-β-lemma↑ (Π t ▹ t₁) = cong₂ Π_▹_ (wk-β-lemma↑ t) (subst-liftSubst t₁ substVar-wk-β-lemma↑)
wk-β-lemma↑ ℕ = refl
wk-β-lemma↑ (var x) = substVar-wk-β-lemma↑ x
wk-β-lemma↑ (lam t) = cong lam (subst-liftSubst t substVar-wk-β-lemma↑)
wk-β-lemma↑ (t ∘ t₁) = cong₂ _∘_ (wk-β-lemma↑ t) (wk-β-lemma↑ t₁)
wk-β-lemma↑ zero = refl
wk-β-lemma↑ (suc t) = cong suc (wk-β-lemma↑ t)
wk-β-lemma↑ (natrec t t₁ t₂ t₃) = cong₄ natrec (subst-liftSubst t substVar-wk-β-lemma↑) (wk-β-lemma↑ t₁) (wk-β-lemma↑ t₂) (wk-β-lemma↑ t₃)

wk-β↑ : ∀ {pr a} t → wk (lift pr) (t [ a ]↑) ≡ wk (lift pr) t [ wk (lift pr) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t) (wk-β-lemma↑ t)))

-- Natrec beta-reduction weakening

substVar-natrec-lemma : ∀ {pr} → (n : Nat) →
      purge (lift pr)
      (wkSubst (step id) (consSubst (wk1Subst idSubst) (suc (var zero))))
      n
      ≡
      wkSubst (step (lift pr))
      (consSubst (wk1Subst var) (suc (var zero))) n
substVar-natrec-lemma zero = refl
substVar-natrec-lemma (suc n) = refl

natrec-lemma : ∀ {pr} G → subst
      (purge (lift pr)
       (wkSubst (step id)
        (consSubst (wk1Subst idSubst) (suc (var zero)))))
      G
      ≡
      subst
      (wkSubst (step (lift pr))
       (consSubst (wk1Subst var) (suc (var zero))))
      G
natrec-lemma U = refl
natrec-lemma (Π G ▹ G₁) = cong₂ Π_▹_ (natrec-lemma G) (subst-liftSubst G₁ substVar-natrec-lemma)
natrec-lemma ℕ = refl
natrec-lemma (var x) = substVar-natrec-lemma x
natrec-lemma (lam G) = cong lam (subst-liftSubst G substVar-natrec-lemma)
natrec-lemma (G ∘ G₁) = cong₂ _∘_ (natrec-lemma G) (natrec-lemma G₁)
natrec-lemma zero = refl
natrec-lemma (suc G) = cong suc (natrec-lemma G)
natrec-lemma (natrec G G₁ G₂ G₃) = cong₄ natrec (subst-liftSubst G substVar-natrec-lemma) (natrec-lemma G₁) (natrec-lemma G₂) (natrec-lemma G₃)

wk-β-natrec : ∀ pr G →
      Π ℕ ▹
      (Π wk (lift pr) G ▹
       wk (lift (lift pr)) (wk1 (G [ suc (var zero) ]↑)))
      ≡
      Π ℕ ▹
      (wk (lift pr) G ▹▹
       wk (lift pr) G [ suc (var zero) ]↑)
wk-β-natrec pr G = cong₂ Π_▹_ refl (cong₂ Π_▹_ refl (trans (wk-comp-comm (lift (lift pr)) (step id) (subst (consSubst (wk1Subst var) (suc (var zero))) G)) (trans (wk-subst G) (sym (trans (wk-subst (wk (lift pr) G)) (trans (subst-wk G) (natrec-lemma G)))))))
