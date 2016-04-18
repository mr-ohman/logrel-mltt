module Definition.Typed.Properties where

open import Data.Product

open import Tools.Context
open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)


-- Wellformed context extraction

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕ x) = x
wfTerm (Π x ▹ x₁) = wfTerm x
wfTerm (var x x₁) = x
wfTerm (lam x) with wfTerm x
wfTerm (lam x₁) | q ∙ x = q
wfTerm (x ∘ x₁) = wfTerm x₁
wfTerm (zero x) = x
wfTerm (suc x) = wfTerm x
wfTerm (natrec x x₁ x₂) = wfTerm x₁
wfTerm (conv x x₁) = wfTerm x

wf : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wf (ℕ x) = x
wf (U x) = x
wf (Π x ▹ x₁) = wf x
wf (univ x) = wfTerm x

wfEqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl x) = wfTerm x
wfEqTerm (sym x) = wfEqTerm x
wfEqTerm (trans x x₁) = wfEqTerm x
wfEqTerm (conv x x₁) = wfEqTerm x
wfEqTerm (Π-cong x x₁) = wfEqTerm x
wfEqTerm (app-cong x x₁) = wfEqTerm x
wfEqTerm (β-red x x₁) = wfTerm x₁
wfEqTerm (fun-ext x x₁ x₂) = wfTerm x
wfEqTerm (suc-cong x) = wfEqTerm x
wfEqTerm (natrec-cong x x₁ x₂) = wfEqTerm x₂
wfEqTerm (natrec-zero x x₁ x₂) = wfTerm x₁
wfEqTerm (natrec-suc x x₁ x₂ x₃) = wfTerm x

wfEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ x) = wfEqTerm x
wfEq (refl x) = wf x
wfEq (sym x) = wfEq x
wfEq (trans x x₁) = wfEq x
wfEq (Π-cong x x₁) = wfEq x

-- Conversion to type/term arrows

eqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
eqTerm (refl x) = x , x
eqTerm (sym t₂) = swap (eqTerm t₂)
eqTerm (trans t₁ t₂) = let a , b = eqTerm t₁
                           c , d = eqTerm t₂
                       in a , d
eqTerm (conv t₁ x) = let a , b = eqTerm t₁
                     in  conv a x , conv b x
eqTerm (Π-cong t t₁) = let a , b = eqTerm t
                           c , d = eqTerm t₁
                       in  Π a ▹ c , Π b ▹ {!d!}
eqTerm (app-cong t t₁) = let a , b = eqTerm t
                             c , d = eqTerm t₁
                         in  a ∘ c , {!b!} ∘ d
eqTerm (β-red x x₁) = lam x ∘ x₁ , {!!}
eqTerm (fun-ext x x₁ t) = x , x₁
eqTerm (natrec-cong x t t₁) = let a , b = eqTerm t
                                  c , d = eqTerm t₁
                              in  (natrec {!!} a c) , {!!}
eqTerm (natrec-zero x x₁ x₂) = natrec x x₁ x₂ ∘ zero (wfTerm x₁) , x₁
eqTerm (natrec-suc x x₁ x₂ x₃) = natrec x₁ x₂ x₃ ∘ suc x
                               , ({!x₃!} ∘ x) ∘ (natrec x₁ x₂ x₃ ∘ x)
eqTerm (suc-cong t) = let a , b = eqTerm t
                      in  suc a , suc b

eq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
eq (univ x) = let a , b = eqTerm x
              in univ a , univ b
eq (refl x) = x , x
eq (sym e) = swap (eq e)
eq (trans e e₁) = let a , b = eq e
                      c , d = eq e₁
                  in  a , d
eq (Π-cong e e₁) = let a , b = eq e
                       c , d = eq e₁
                   in  Π a ▹ c , Π b ▹ {!d!}

substEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A → Γ ⊢ B
substEq e _ = proj₂ (eq e)

-- Term to type arrow

typeOfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ A
typeOfTerm (var x₁ x₂) = {!!}
typeOfTerm (ℕ x) = U x
typeOfTerm (Π t ▹ t₁) = U (wfTerm t)
typeOfTerm (lam t₁) with wfTerm t₁
typeOfTerm (lam t₁) | x ∙ x₁ = Π x₁ ▹ typeOfTerm t₁
typeOfTerm (t ∘ t₁) = {!!}
typeOfTerm (zero x) = ℕ x
typeOfTerm (suc t) = typeOfTerm t
typeOfTerm (natrec x t t₁) = Π ℕ (wfTerm t) ▹ x
typeOfTerm (conv t₁ x) = substEq x (typeOfTerm t₁)

-- Weakening

mutual
  wkIndex : ∀ {Γ Δ x A} → Γ ⊆ Δ → ⊢ Δ → x ∷ A ∈ Γ → ∃ λ y → y ∷ A ∈ Δ
  wkIndex base ⊢Δ ()
  wkIndex (step pr) (⊢Δ ∙ x) i = let y = wkIndex pr ⊢Δ i
                                 in suc (proj₁ y) , there {!proj₂ y!}
  wkIndex (lift pr) ⊢Δ here = zero , here
  wkIndex (lift pr) (⊢Δ ∙ x) (there i) = let y = wkIndex pr ⊢Δ i
                                         in suc (proj₁ y) , there (proj₂ y)

  -- To weaken typed terms, we need to weaken untyped terms most likely
  wk : ∀ {Γ Δ A} → (pr : Γ ⊆ Δ) → ⊢ Δ → Γ ⊢ A → Δ ⊢ U.wk (untype-⊆ pr) A
  -- wk : ∀ {Γ Δ A} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ A → Δ ⊢ A
  wk pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wk pr ⊢Δ (U x) = U ⊢Δ
  wk pr ⊢Δ (Π A ▹ A₁) = let x = wk pr ⊢Δ A
                         in  Π x ▹ wk (lift pr) (⊢Δ ∙ x) {!A₁!}
  wk pr ⊢Δ (univ x) = {!!} --univ (wkTerm pr ⊢Δ x)

  wkTerm : ∀ {Γ Δ A t} → Γ ⊆ Δ → ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  wkTerm pr ⊢Δ (var x₁ x₂) = var ⊢Δ {!!}  --(wkIndex pr ⊢Δ x₂)
  wkTerm pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wkTerm pr ⊢Δ (Π t ▹ t₁) =
    let x = wkTerm pr ⊢Δ t
    in  Π x ▹ wkTerm (lift pr) (⊢Δ ∙ univ x) t₁
  wkTerm pr ⊢Δ (lam t₁) = lam (wkTerm (lift pr) (⊢Δ ∙ {!!}) t₁)
  wkTerm pr ⊢Δ (t ∘ t₁) = wkTerm pr ⊢Δ t ∘ wkTerm pr ⊢Δ t₁
  wkTerm pr ⊢Δ (zero x) = zero ⊢Δ
  wkTerm pr ⊢Δ (suc t) = suc (wkTerm pr ⊢Δ t)
  wkTerm pr ⊢Δ (natrec x t t₁) = {!!}
  wkTerm pr ⊢Δ (conv t₁ x) = {!!}

-- Inverse typing lemmas

inversion-zero : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zero x) = refl (ℕ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

inversion-suc : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ C ≡ ℕ
inversion-suc (suc x) = refl (ℕ (wfTerm x))
inversion-suc (conv x x₁) = trans (sym x₁) (inversion-suc x)

inversion-natrec : ∀ {Γ c g A C} → Γ ⊢ natrec C c g ∷ A → Γ ⊢ A ≡ Π ℕ ▹ C
inversion-natrec (natrec x d d₁) = Π-cong (refl (ℕ (wfTerm d))) (refl x)
inversion-natrec (conv d x) = trans (sym x) (inversion-natrec d)

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ d₁) = _ , _ , d , d₁ , refl (typeOfTerm (d ∘ d₁))
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e

-- Π-injectivity needed to prove this?
inversion-app-natrec : ∀ {Γ c g m A C} → Γ ⊢ natrec C c g ∘ m ∷ A
                     → Γ ⊢ A ≡ C [ m ]
inversion-app-natrec (x ∘ x₁) = {!!}
inversion-app-natrec (conv x x₁) = trans (sym x₁) (inversion-app-natrec x)

-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst x x₁ x₂ x₃) =
  app-cong (refl (conv (natrec x x₁ x₂) (Π-cong (refl (ℕ (wfTerm x₁))) {!!})))
               (subsetTerm x₃)
subsetTerm (natrec-zero x x₁ x₂) = natrec-zero x x₁ x₂
subsetTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc x x₁ x₂ x₃
subsetTerm (app-subst x x₁) = app-cong (subsetTerm x) (refl x₁)
subsetTerm (β-red x x₁) = β-red x x₁
subsetTerm (conv x x₁) = conv (subsetTerm x) x₁

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ x) = univ (subsetTerm x)
