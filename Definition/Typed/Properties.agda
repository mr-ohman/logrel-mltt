module Definition.Typed.Properties where

open import Data.Product

open import Tools.Context
open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)

-- -- DO NOT HOLD IN GENERAL
-- mutual
--   weaken-⊢Γ : ∀ {Γ Δ} → Γ ⊆ Δ → ⊢ Δ → ⊢ Γ
--   weaken-⊢Γ base ε = ε
--   weaken-⊢Γ (step x) (c ∙ x₁) = weaken-⊢Γ x c
--   weaken-⊢Γ (pop! x) (c ∙ x₁) = weaken-⊢Γ x c ∙ weaken-Γ⊢A x x₁

--   weaken-Γ⊢A : ∀ {Γ Δ A} → Γ ⊆ Δ → Δ ⊢ A → Γ ⊢ A
--   weaken-Γ⊢A x (ℕ-i x₁) = ℕ-i (weaken-⊢Γ x x₁)
--   weaken-Γ⊢A x (U-i x₁) = U-i (weaken-⊢Γ x x₁)
--   weaken-Γ⊢A x (Π-i t t₁) = Π-i (weaken-Γ⊢A x t) (weaken-Γ⊢A (pop! x) t₁)
--   weaken-Γ⊢A x (univ-refl-term x₁) = univ-refl-term (weaken-Γ⊢t∷A x x₁)

--   weaken-Γ⊢t∷A : ∀ {Γ Δ A t} → Γ ⊆ Δ → Δ ⊢ t ∷ A → Γ ⊢ t ∷ A
--   weaken-Γ⊢t∷A x t = {!!}

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (var-i x x₁) = x
wfTerm (univ-ℕ-i x) = x
wfTerm (univ-Π-i x x₁) = wfTerm x
wfTerm (λ-i x) with wfTerm x
wfTerm (λ-i x₁) | q ∙ x = q
wfTerm (fun-e x x₁) = wfTerm x₁
wfTerm (zero x) = x
wfTerm (suc x) = wfTerm x
wfTerm (natrec-i x x₁ x₂) = wfTerm x₁
wfTerm (eq-type-term x x₁) = wfTerm x

wf : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wf (ℕ-i x) = x
wf (U-i x) = x
wf (Π-i x x₁) = wf x
wf (univ-refl-term x) = wfTerm x

wfHead : ∀ {Γ A} → ⊢ Γ ∙ A → Γ ⊢ A
wfHead (Γ₁ ∙ x) = x

eqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
eqTerm (refl x) = x , x
eqTerm (sym t₂) = swap (eqTerm t₂)
eqTerm (trans t₁ t₂) = let a , b = eqTerm t₁
                           c , d = eqTerm t₂
                       in a , d
eqTerm (eq-type-term t₁ x) = let a , b = eqTerm t₁
                             in  eq-type-term a x , eq-type-term b x
eqTerm (Π-eq-univ t t₁) = let a , b = eqTerm t
                              c , d = eqTerm t₁
                          in  univ-Π-i a c , univ-Π-i b {!d!}
eqTerm (fun-eq t t₁) = let a , b = eqTerm t
                           c , d = eqTerm t₁
                       in  fun-e a c , fun-e {!b!} d
eqTerm (β-red x x₁) = fun-e (λ-i x) x₁ , {!!}
eqTerm (fun-ext x x₁ t) = x , x₁
eqTerm (natrec-eq x t t₁) = let a , b = eqTerm t
                                c , d = eqTerm t₁
                            in  (natrec-i {!!} a c) , {!!}
eqTerm (natrec-zero x x₁ x₂) = (fun-e (natrec-i x x₁ x₂) (zero (wfTerm x₁))) , x₁
eqTerm (natrec-suc x x₁ x₂ x₃) = fun-e (natrec-i x₁ x₂ x₃) (suc x)
                               , fun-e (fun-e {!x₃!} x) (fun-e (natrec-i x₁ x₂ x₃) x)
eqTerm (suc-cong t) = let a , b = eqTerm t
                      in  suc a , suc b

eq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
eq (univ-refl x) = let a , b = eqTerm x
                   in univ-refl-term a , univ-refl-term b
eq (refl x) = x , x
eq (sym e) = swap (eq e)
eq (trans e e₁) = let a , b = eq e
                      c , d = eq e₁
                  in a , d
eq (Π-eq e e₁) = let a , b = eq e
                     c , d = eq e₁
                 in  Π-i a c , Π-i b {!d!}

substEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A → Γ ⊢ B
substEq e _ = proj₂ (eq e)

typeOfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ A
typeOfTerm (var-i x₁ x₂) = {!!}
typeOfTerm (univ-ℕ-i x) = U-i x
typeOfTerm (univ-Π-i t t₁) = U-i (wfTerm t)
typeOfTerm (λ-i t₁) = Π-i (wfHead (wfTerm t₁)) (typeOfTerm t₁)
typeOfTerm (fun-e t t₁) = {!!}
typeOfTerm (zero x) = ℕ-i x
typeOfTerm (suc t) = typeOfTerm t
typeOfTerm (natrec-i x t t₁) = Π-i (ℕ-i (wfTerm t)) x
typeOfTerm (eq-type-term t₁ x) = substEq x (typeOfTerm t₁)

mutual
  wkIndex : ∀ {Γ Δ x A} → Γ ⊆ Δ → ⊢ Δ → x ∷ A ∈ Γ → ∃ λ y → y ∷ A ∈ Δ
  wkIndex base ⊢Δ ()
  wkIndex (step pr) (⊢Δ ∙ x) i = let y = wkIndex pr ⊢Δ i
                                 in suc (proj₁ y) , there {!proj₂ y!}
  wkIndex (lift pr) ⊢Δ here = zero , here
  wkIndex (lift pr) (⊢Δ ∙ x) (there i) = let y = wkIndex pr ⊢Δ i
                                         in suc (proj₁ y) , there (proj₂ y)

  wk : ∀ {Γ Δ A} → (pr : Γ ⊆ Δ) → ⊢ Δ → Γ ⊢ A → Δ ⊢ U.wk (untype-⊆ pr) A
  -- wk : ∀ {Γ Δ A} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ A → Δ ⊢ A
  wk pr ⊢Δ (ℕ-i x) = ℕ-i ⊢Δ
  wk pr ⊢Δ (U-i x) = U-i ⊢Δ
  wk pr ⊢Δ (Π-i A A₁) = let x = wk pr ⊢Δ A
                        in  Π-i x (wk (lift pr) (⊢Δ ∙ x) {!A₁!})
  wk pr ⊢Δ (univ-refl-term x) = {!!} --univ-refl-term (wkTerm pr ⊢Δ x)

  -- To weaken typed terms, we need to weaken untyped terms most likely
  wkTerm : ∀ {Γ Δ A t} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  wkTerm pr ⊢Δ (var-i x₁ x₂) = var-i ⊢Δ {!!}  --(wkIndex pr ⊢Δ x₂)
  wkTerm pr ⊢Δ (univ-ℕ-i x) = univ-ℕ-i ⊢Δ
  wkTerm pr ⊢Δ (univ-Π-i t t₁) =
    let x = wkTerm pr ⊢Δ t
    in  univ-Π-i x (wkTerm (lift pr) (⊢Δ ∙ univ-refl-term x) t₁)
  wkTerm pr ⊢Δ (λ-i t₁) = λ-i (wkTerm (lift pr) (⊢Δ ∙ {!!}) t₁)
  wkTerm pr ⊢Δ (fun-e t t₁) = fun-e (wkTerm pr ⊢Δ t) (wkTerm pr ⊢Δ t₁)
  wkTerm pr ⊢Δ (zero x) = zero ⊢Δ
  wkTerm pr ⊢Δ (suc t) = suc (wkTerm pr ⊢Δ t)
  wkTerm pr ⊢Δ (natrec-i x t t₁) = {!!}
  wkTerm pr ⊢Δ (eq-type-term t₁ x) = {!!}

inversion-natrec :  ∀ {Γ c g A C} → Γ ⊢ natrec C c g ∷ A → Γ ⊢ A ≡ Π ℕ ▹ C
inversion-natrec (natrec-i x d d₁) = Π-eq (refl (ℕ-i (wfTerm d))) (refl x)
inversion-natrec (eq-type-term d x) = trans (sym x) (inversion-natrec d)

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (fun-e d d₁) = _ , _ , d , d₁ , refl (typeOfTerm (fun-e d d₁))
inversion-app (eq-type-term d x) = let a , b , c , d , e = inversion-app d
                                   in  a , b , c , d , trans (sym x) e

-- inverse typing lemmas
lemma1 : ∀ {Γ c g m A C} → Γ ⊢ natrec C c g ∘ m ∷ A → Γ ⊢ A ≡ C [ m ]
lemma1 (fun-e x x₁) = {!!}
lemma1 (eq-type-term x x₁) = trans (sym x₁) (lemma1 x)

lemmaℕ0 : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
lemmaℕ0 (zero x) = refl (ℕ-i x)
lemmaℕ0 (eq-type-term x x₁) = trans (sym x₁) (lemmaℕ0 x)

lemmaℕ : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ C ≡ ℕ
lemmaℕ (suc x) = refl (ℕ-i (wfTerm x))
lemmaℕ (eq-type-term x x₁) = trans (sym x₁) (lemmaℕ x)

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst x x₁ x₂ x₃) =
  fun-eq (refl (eq-type-term (natrec-i x x₁ x₂) (Π-eq (refl (ℕ-i (wfTerm x₁))) {!!})))
               (subsetTerm x₃)
subsetTerm (natrec-zero x x₁ x₂) = natrec-zero x x₁ x₂
subsetTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc x x₁ x₂ x₃
subsetTerm (app-subst x x₁) = fun-eq (subsetTerm x) (refl x₁)
subsetTerm (β-red x x₁) = β-red x x₁
subsetTerm (eq-type-term x x₁) = eq-type-term (subsetTerm x) x₁

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ-refl x) = univ-refl (subsetTerm x)
