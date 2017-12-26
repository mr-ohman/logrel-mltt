{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.FullReduction where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  data NfNeutral : Term → Set where
    var    : ∀ n                              → NfNeutral (var n)
    _∘_    : ∀ {k u}     → NfNeutral k → Nf u → NfNeutral (k ∘ u)
    natrec : ∀ {C c g k} → Nf C → Nf c → Nf g → NfNeutral k
                                              → NfNeutral (natrec C c g k)

  data Nf : Term → Set where

    U    : Nf U
    Π    : ∀ {A B} → Nf A → Nf B → Nf (Π A ▹ B)
    ℕ    : Nf ℕ

    lam  : ∀ {t} → Nf t → Nf (lam t)
    zero : Nf zero
    suc  : ∀ {t} → Nf t → Nf (suc t)

    ne   : ∀ {n} → NfNeutral n → Nf n


mutual
  fullRedNe : ∀ {t A Γ} → Γ ⊢ t ~ t ↑ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe (var x₁ x₂) = var _ , var _ , refl x₁
  fullRedNe (app x x₁) =
    let t′ , nfT , t≡t′ = fullRedNe′ x
        u′ , nfU , u≡u′ = fullRedTerm x₁
    in  (t′ ∘ u′) , (nfT ∘ nfU) , app-cong t≡t′ u≡u′
  fullRedNe (natrec x x₁ x₂ x₃) =
    let q , w , e = fullRed x
        a , s , d = fullRedTerm x₁
        z , c , v = fullRedTerm x₂
        r , t , y = fullRedNe′ x₃
    in  natrec q a z r , natrec w s c t , natrec-cong e d v y

  fullRedNe′ : ∀ {t A Γ} → Γ ⊢ t ~ t ↓ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe′ ([~] A D whnfB k~l) =
    let u , nf , t≡u = fullRedNe k~l
    in  u , nf , conv t≡u (subset* D)

  fullRed : ∀ {A Γ} → Γ ⊢ A [conv↑] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) rewrite whrDet* (D , whnfA′) (D′ , whnfB′) =
    let q , w , e = fullRed′ A′<>B′
    in  q , w , trans (subset* D′) e

  fullRed′ : ∀ {A Γ} → Γ ⊢ A [conv↓] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed′ (U-refl x) = U , U , refl (U x)
  fullRed′ (ℕ-refl x) = ℕ , ℕ , refl (ℕ x)
  fullRed′ (ne x) =
    let u , nf , t≡u = fullRedNe′ x
    in  u , ne nf , univ t≡u
  fullRed′ (Π-cong x x₁ x₂) =
    let q , w , e = fullRed x₁
        a , s , d = fullRed x₂
    in  Π q ▹ a , Π w s , Π-cong x e d

  fullRedTerm : ∀ {t A Γ} → Γ ⊢ t [conv↑] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) rewrite whrDet*Term (d , whnft′) (d′ , whnfu′) =
    let q , w , r = fullRedTerm′ t<>u
    in  q , w , conv (trans (subset*Term d′) r) (sym (subset* D))

  fullRedTerm′ : ∀ {t A Γ} → Γ ⊢ t [conv↓] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm′ (ℕ-ins x) =
    let q , w , e = fullRedNe′ x
    in  q , ne w , e
  fullRedTerm′ (ne-ins x x₁ x₂ x₃) =
    let q , w , e = fullRedNe′ x₃
        _ , r , _ = syntacticEqTerm e
        _ , t , _ = ne~↓ x₃
    in  q , ne w , conv e (neTypeEq t r x)
  fullRedTerm′ (univ x x₁ x₂) =
    let q , w , e = fullRed′ x₂
    in  q , w , inverseUnivEq x e
  fullRedTerm′ (zero-refl x) = zero , zero , refl (zero x)
  fullRedTerm′ (suc-cong x) =
    let q , w , e = fullRedTerm x
    in  suc q , suc w , suc-cong e
  fullRedTerm′ (η-eq ⊢F ⊢t x₂ x₃ x₄ x₅) =
    let q , w , e = fullRedTerm x₅
        _ , _ , ⊢q = syntacticEqTerm e
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢q = wkTerm (lift (step id)) ΓFF'⊢ ⊢q
    in  lam q , lam w ,
        η-eq ⊢F ⊢t (lam ⊢F ⊢q)
             (trans e (PE.subst₂ (λ x y → _ ⊢ x ≡ lam (U.wk (lift (step id)) q) ∘ var 0 ∷ y)
                                 (wkSingleSubstId q) (wkSingleSubstId _)
                                 (sym (β-red wk⊢F wk⊢q (var ΓF⊢ here)))))
