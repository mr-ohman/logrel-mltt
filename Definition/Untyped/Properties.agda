module Definition.Untyped.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List using (List; []; _∷_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality as PE hiding ([_]; subst)

open import Definition.Untyped


-- Proofs that single substitutions works as expected with lambda.

subst-test₁ : {x : Term} → lam (var 0) [ x ] ≡ lam (var 0)
subst-test₁ = refl

subst-test₂ : {x : Term} → lam (var 1) [ x ] ≡ lam (wk1 x)
subst-test₂ = refl

cong₃ : ∀ {a b c d}
          {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          {x y u v a b}
        (f : A → B → C → D) → x ≡ y → u ≡ v → a ≡ b
      → f x u a ≡ f y v b
cong₃ f refl refl refl = refl

cong₄ : ∀ {a b c d e}
          {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
          {x y u v s t q r}
        (f : A → B → C → D → E) → x ≡ y → u ≡ v → s ≡ t → q ≡ r
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
wk-id (natrec x x₁ x₂ x₃) n =
  cong₄ natrec (wk-id x (suc n)) (wk-id x₁ n) (wk-id x₂ n) (wk-id x₃ n)

idSubst-lemma-var : (m n : Nat) → substVar (arbLifts n) m ≡ var m
idSubst-lemma-var m zero = refl
idSubst-lemma-var zero (suc n) = refl
idSubst-lemma-var (suc m) (suc n) = cong (wk (step id)) (idSubst-lemma-var m n)

idSubst-lemma : (t : Term) (n : Nat) → subst (arbLifts n) t ≡ t
idSubst-lemma U n = refl
idSubst-lemma (Π t ▹ t₁) n =
  cong₂ Π_▹_ (idSubst-lemma t n) (idSubst-lemma t₁ (suc n))
idSubst-lemma ℕ n = refl
idSubst-lemma (var x) n = idSubst-lemma-var x n
idSubst-lemma (lam t) n = cong lam (idSubst-lemma t (suc n))
idSubst-lemma (t ∘ t₁) n = cong₂ _∘_ (idSubst-lemma t n) (idSubst-lemma t₁ n)
idSubst-lemma zero n = refl
idSubst-lemma (suc t) n = cong suc (idSubst-lemma t n)
idSubst-lemma (natrec t t₁ t₂ t₃) n =
  cong₄ natrec (idSubst-lemma t (suc n)) (idSubst-lemma t₁ n)
               (idSubst-lemma t₂ n) (idSubst-lemma t₃ n)

idSubst-lemma₀ : (t : Term) → subst idSubst t ≡ t
idSubst-lemma₀ t = idSubst-lemma t zero


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
wk-comp-comm p q (Π t ▹ t₁) =
  cong₂ Π_▹_ (wk-comp-comm p q t) (wk-comp-comm (lift p) (lift q) t₁)
wk-comp-comm p q ℕ = refl
wk-comp-comm p q (var x) = cong var (wkNat-comp-comm p q x)
wk-comp-comm p q (lam t) = cong lam (wk-comp-comm (lift p) (lift q) t)
wk-comp-comm p q (t ∘ t₁) = cong₂ _∘_ (wk-comp-comm p q t) (wk-comp-comm p q t₁)
wk-comp-comm p q zero = refl
wk-comp-comm p q (suc t) = cong suc (wk-comp-comm p q t)
wk-comp-comm p q (natrec t t₁ t₂ t₃) =
  cong₄ natrec (wk-comp-comm (lift p) (lift q) t)
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

liftSubstEq : ∀ {σ σ'} → ((x : Nat) → σ x ≡ σ' x)
            → (x : Nat) → liftSubst σ x ≡ liftSubst σ' x
liftSubstEq eq zero = refl
liftSubstEq eq (suc x) = cong wk1 (eq x)

substEq : ∀ {σ σ'} → ((x : Nat) → σ x ≡ σ' x)
        → (t : Term) → subst σ t ≡ subst σ' t
substEq eq U = refl
substEq eq (Π t ▹ t₁) = cong₂ Π_▹_ (substEq eq t) (substEq (liftSubstEq eq) t₁)
substEq eq ℕ = refl
substEq eq (var x₁) = eq x₁
substEq eq (lam t) = cong lam (substEq (liftSubstEq eq) t)
substEq eq (t ∘ t₁) = cong₂ _∘_ (substEq eq t) (substEq eq t₁)
substEq eq zero = refl
substEq eq (suc t) = cong suc (substEq eq t)
substEq eq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (substEq (liftSubstEq eq) t) (substEq eq t₁)
               (substEq eq t₂) (substEq eq t₃)

liftIdSubst : (x : Nat) → (liftSubst idSubst) x ≡ idSubst x
liftIdSubst zero = refl
liftIdSubst (suc x) = refl

substIdEq : (t : Term) → subst idSubst t ≡ t
substIdEq U = refl
substIdEq (Π t ▹ t₁) =
  cong₂ Π_▹_ (substIdEq t) (trans (substEq liftIdSubst t₁) (substIdEq t₁))
substIdEq ℕ = refl
substIdEq (var x) = refl
substIdEq (lam t) = cong lam (trans (substEq liftIdSubst t) (substIdEq t))
substIdEq (t ∘ t₁) = cong₂ _∘_ (substIdEq t) (substIdEq t₁)
substIdEq zero = refl
substIdEq (suc t) = cong suc (substIdEq t)
substIdEq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (substEq liftIdSubst t) (substIdEq t))
               (substIdEq t₁) (substIdEq t₂) (substIdEq t₃)

wkSubst-liftSubst : ∀ {pr ρ} n
                  → (wkSubst (lift pr) (liftSubst ρ)) n
                  ≡ (liftSubst (wkSubst pr ρ)) n
wkSubst-liftSubst zero = refl
wkSubst-liftSubst (suc n) = sym (wkIndex-lift _)

purge-liftSubst : ∀ {pr ρ} (n : Nat)
                → (purge (lift pr) (liftSubst ρ)) n
                ≡ (liftSubst (purge pr ρ)) n
purge-liftSubst zero = refl
purge-liftSubst (suc n) = refl

wk-subst : ∀ {pr ρ} t → wk pr (subst ρ t) ≡ subst (wkSubst pr ρ) t
wk-subst U = refl
wk-subst (Π t ▹ t₁) =
  cong₂ Π_▹_ (wk-subst t) (trans (wk-subst t₁) (substEq wkSubst-liftSubst t₁))
wk-subst ℕ = refl
wk-subst (var x) = refl
wk-subst (lam t) = cong lam (trans (wk-subst t) (substEq wkSubst-liftSubst t))
wk-subst (t ∘ t₁) = cong₂ _∘_ (wk-subst t) (wk-subst t₁)
wk-subst zero = refl
wk-subst (suc t) = cong suc (wk-subst t)
wk-subst (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (wk-subst t) (substEq wkSubst-liftSubst t))
               (wk-subst t₁) (wk-subst t₂) (wk-subst t₃)

subst-wk : ∀ {pr ρ} t → subst ρ (wk pr t) ≡ subst (purge pr ρ) t
subst-wk U = refl
subst-wk (Π t ▹ t₁) =
  cong₂ Π_▹_ (subst-wk t) (trans (subst-wk t₁) (substEq purge-liftSubst t₁))
subst-wk ℕ = refl
subst-wk (var x) = refl
subst-wk (lam t) = cong lam (trans (subst-wk t) (substEq purge-liftSubst t))
subst-wk (t ∘ t₁) = cong₂ _∘_ (subst-wk t) (subst-wk t₁)
subst-wk zero = refl
subst-wk (suc t) = cong suc (subst-wk t)
subst-wk (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (subst-wk t) (substEq purge-liftSubst t))
               (subst-wk t₁) (subst-wk t₂) (subst-wk t₃)

-- Beta reduction weakening

wk-β-lemma : ∀ {pr a} (n : Nat) →
      purge (lift pr) (consSubst idSubst (wk pr a)) n ≡
      wkSubst pr (consSubst idSubst a) n
wk-β-lemma zero = refl
wk-β-lemma (suc n) = refl

wk-β : ∀ {pr a} t → wk pr (t [ a ]) ≡ wk (lift pr) t [ wk pr a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t) (substEq wk-β-lemma t)))

wk-β-lemma↑ : ∀ {pr a} (n : Nat) →
      purge (lift pr) (consSubst (wk1Subst idSubst) (wk (lift pr) a)) n ≡
      wkSubst (lift pr) (consSubst (wk1Subst idSubst) a) n
wk-β-lemma↑ zero = refl
wk-β-lemma↑ (suc n) = refl

wk-β↑ : ∀ {ρ a} t → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t) (substEq wk-β-lemma↑ t)))

-- Natrec beta-reduction weakening

natrec-lemma : ∀ {pr} → (n : Nat) →
      purge (lift pr)
      (wkSubst (step id) (consSubst (wk1Subst idSubst) (suc (var zero))))
      n
      ≡
      wkSubst (step (lift pr))
      (consSubst (wk1Subst var) (suc (var zero))) n
natrec-lemma zero = refl
natrec-lemma (suc n) = refl

wk-β-natrec : ∀ ρ G →
      Π ℕ ▹
      (Π wk (lift ρ) G ▹
       wk (lift (lift ρ)) (wk1 (G [ suc (var zero) ]↑)))
      ≡
      Π ℕ ▹
      (wk (lift ρ) G ▹▹
       wk (lift ρ) G [ suc (var zero) ]↑)
wk-β-natrec ρ G =
  cong₂ Π_▹_ refl
        (cong₂ Π_▹_ refl
               (trans (wk-comp-comm (lift (lift ρ)) (step id)
                                    (subst (consSubst (wk1Subst var)
                                                      (suc (var zero)))
                                           G))
                      (trans (wk-subst G)
                             (sym (trans (wk-subst (wk (lift ρ) G))
                                         (trans (subst-wk G)
                                                (substEq natrec-lemma G)))))))

substCompLift : ∀ {σ σ'} (x : Nat)
              → (substComp (liftSubst σ') (liftSubst σ)) x
              ≡ (liftSubst (substComp σ' σ)) x
substCompLift zero = refl
substCompLift {σ} {σ'} (suc x) = trans (subst-wk (σ' x)) (sym (wk-subst (σ' x)))

substCompEq : ∀ {σ σ'} (t : Term)
            → subst σ (subst σ' t) ≡ subst (substComp σ' σ) t
substCompEq U = refl
substCompEq (Π t ▹ t₁) =
  cong₂ Π_▹_ (substCompEq t) (trans (substCompEq t₁) (substEq substCompLift t₁))
substCompEq ℕ = refl
substCompEq (var x) = refl
substCompEq (lam t) = cong lam (trans (substCompEq t) (substEq substCompLift t))
substCompEq (t ∘ t₁) = cong₂ _∘_ (substCompEq t) (substCompEq t₁)
substCompEq zero = refl
substCompEq (suc t) = cong suc (substCompEq t)
substCompEq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (substCompEq t) (substEq substCompLift t))
               (substCompEq t₁) (substCompEq t₂) (substCompEq t₃)

substConcatSingleton : ∀ {a σ} (x : Nat)
                     → (substComp (liftSubst σ) (consSubst idSubst a)) x
                     ≡ (consSubst σ a) x
substConcatSingleton zero = refl
substConcatSingleton {σ = σ} (suc x) = trans (subst-wk (σ x)) (substIdEq (σ x))

substConcatSingleton' : ∀ {a σ} (x : Nat)
                      → (substComp (consSubst idSubst a) σ) x
                      ≡ (consSubst σ (subst σ a)) x
substConcatSingleton' zero = refl
substConcatSingleton' (suc x) = refl

substConcatSingleton'' : ∀ {a σ} (x : Nat)
                       → (substComp (consSubst (wk1Subst idSubst) a) σ) x
                       ≡ (consSubst (tail σ) (subst σ a)) x
substConcatSingleton'' zero = refl
substConcatSingleton'' (suc x) = refl

singleSubstLemma : ∀ a σ G → (subst (liftSubst σ) G) [ a ] ≡
     subst (consSubst σ a) G
singleSubstLemma a σ G = trans (substCompEq G) (substEq substConcatSingleton G)

G-substWkLemma : ∀ {ρ} a σ G → wk (lift ρ) (subst (liftSubst σ) G) [ a ] ≡
     subst (consSubst (wkSubst ρ σ) a) G
G-substWkLemma a σ G =
  trans (cong (subst (consSubst var a))
              (trans (wk-subst G) (substEq wkSubst-liftSubst G)))
        (trans (substCompEq G) (substEq substConcatSingleton G))

singleSubstLift : ∀ {σ} G t
                → subst σ (G [ t ]) ≡ subst (liftSubst σ) G [ subst σ t ]
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substEq substConcatSingleton' G)
                      (sym (substEq substConcatSingleton G)))
               (sym (substCompEq G)))

G-lamLemma : ∀ {ρ σ} G
           → wk (lift ρ) (subst (liftSubst σ) G)
           ≡ subst (liftSubst (wkSubst ρ σ)) G
G-lamLemma G = trans (wk-subst G) (substEq wkSubst-liftSubst G)

idWkLiftSubst : ∀ {σ} x
              → (consSubst (wkSubst (step id) σ) (var zero)) x
              ≡ (liftSubst σ) x
idWkLiftSubst zero = refl
idWkLiftSubst (suc x) = refl

idWkLiftSubstLemma : ∀ σ G
      → wk (lift (step id)) (subst (liftSubst σ) G) [ var 0 ]
      ≡ subst (liftSubst σ) G
idWkLiftSubstLemma σ G =
  trans (G-substWkLemma (var zero) σ G) (substEq idWkLiftSubst G)

wk2subst : ∀ ρ A → wk ρ A ≡ subst (wkSubst ρ idSubst) A
wk2subst ρ A = trans (PE.cong (wk ρ) (PE.sym (substIdEq A))) (wk-subst A)

lemma : ∀ σ t x → (substComp (liftSubst σ)
       (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t))) x
       ≡ (substComp (consSubst (wk1Subst idSubst) t) (liftSubst σ)) x
lemma σ t zero = refl
lemma σ t (suc x) = trans (subst-wk (σ x)) (sym (wk2subst (step id) (σ x)))

singleSubstLift↑ : ∀ σ G t
                 → subst (liftSubst σ) (G [ t ]↑)
                 ≡ subst (liftSubst σ) G [ subst (liftSubst σ) t ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substEq (lemma σ t) G)))

lemma2 : ∀ {σ t G}
       → subst (consSubst (λ n → σ (suc n)) (subst (tail σ) t)) G
       ≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
lemma2 {t = t} {G = G} =
  trans (substEq (λ { zero → sym (subst-wk t) ; (suc x) → refl }) G)
        (sym (substCompEq G))
