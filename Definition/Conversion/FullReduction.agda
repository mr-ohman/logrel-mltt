{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.Conversion.FullReduction where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  data NfNeutral : Term → Set where
    var     : ∀ n                              → NfNeutral (var n)
    ∘ₙ      : ∀ {k u}     → NfNeutral k → Nf u → NfNeutral (k ∘ u)
    natrecₙ : ∀ {C c g k} → Nf C → Nf c → Nf g → NfNeutral k
                                               → NfNeutral (natrec C c g k)
    Emptyrecₙ : ∀ {C k} → Nf C → NfNeutral k
                               → NfNeutral (Emptyrec C k)

  data Nf : Term → Set where

    Uₙ    : Nf U
    Πₙ    : ∀ {A B} → Nf A → Nf B → Nf (Π A ▹ B)
    ℕₙ    : Nf ℕ
    Emptyₙ    : Nf Empty

    lamₙ  : ∀ {t} → Nf t → Nf (lam t)
    zeroₙ : Nf zero
    sucₙ  : ∀ {t} → Nf t → Nf (suc t)

    ne   : ∀ {n} → NfNeutral n → Nf n


mutual
  fullRedNe : ∀ {t A Γ} → Γ ⊢ t ~ t ↑ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe (var-refl x _) = var _ , var _ , refl x
  fullRedNe (app-cong t u) =
    let t′ , nfT′ , t≡t′ = fullRedNe′ t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in  (t′ ∘ u′) , (∘ₙ nfT′ nfU′) , app-cong t≡t′ u≡u′
  fullRedNe (natrec-cong C z s n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        z′ , nfZ′ , z≡z′ = fullRedTerm z
        s′ , nfS′ , s≡s′ = fullRedTerm s
        n′ , nfN′ , n≡n′ = fullRedNe′ n
    in  natrec C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
     ,  natrec-cong C≡C′ z≡z′ s≡s′ n≡n′
  fullRedNe (Emptyrec-cong C n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        n′ , nfN′ , n≡n′ = fullRedNe′ n
    in  Emptyrec C′ n′ , Emptyrecₙ nfC′ nfN′
     ,  Emptyrec-cong C≡C′ n≡n′

  fullRedNe′ : ∀ {t A Γ} → Γ ⊢ t ~ t ↓ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe′ ([~] A D whnfB k~l) =
    let u , nf , t≡u = fullRedNe k~l
    in  u , nf , conv t≡u (subset* D)

  fullRed : ∀ {A Γ} → Γ ⊢ A [conv↑] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
    rewrite whrDet* (D , whnfA′) (D′ , whnfB′) =
    let B″ , nf , B′≡B″ = fullRed′ A′<>B′
    in  B″ , nf , trans (subset* D′) B′≡B″

  fullRed′ : ∀ {A Γ} → Γ ⊢ A [conv↓] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed′ (U-refl ⊢Γ) = U , Uₙ , refl (Uⱼ ⊢Γ)
  fullRed′ (ℕ-refl ⊢Γ) = ℕ , ℕₙ , refl (ℕⱼ ⊢Γ)
  fullRed′ (Empty-refl ⊢Γ) = Empty , Emptyₙ , refl (Emptyⱼ ⊢Γ)
  fullRed′ (ne A) =
    let B , nf , A≡B = fullRedNe′ A
    in  B , ne nf , univ A≡B
  fullRed′ (Π-cong ⊢F F G) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  Π F′ ▹ G′ , Πₙ nfF′ nfG′ , Π-cong ⊢F F≡F′ G≡G′

  fullRedTerm : ∀ {t A Γ} → Γ ⊢ t [conv↑] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
    rewrite whrDet*Term (d , whnft′) (d′ , whnfu′) =
    let u″ , nf , u′≡u″ = fullRedTerm′ t<>u
    in  u″ , nf , conv (trans (subset*Term d′) u′≡u″) (sym (subset* D))

  fullRedTerm′ : ∀ {t A Γ} → Γ ⊢ t [conv↓] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm′ (ℕ-ins t) =
    let u , nf , t≡u = fullRedNe′ t
    in  u , ne nf , t≡u
  fullRedTerm′ (Empty-ins t) =
    let u , nf , t≡u = fullRedNe′ t
    in  u , ne nf , t≡u
  fullRedTerm′ (ne-ins ⊢t _ _ t) =
    let u , nfU , t≡u = fullRedNe′ t
        _ , ⊢t∷M , _ = syntacticEqTerm t≡u
        _ , neT , _ = ne~↓ t
    in  u , ne nfU , conv t≡u (neTypeEq neT ⊢t∷M ⊢t)
  fullRedTerm′ (univ ⊢t _ t) =
    let u , nf , t≡u = fullRed′ t
    in  u , nf , inverseUnivEq ⊢t t≡u
  fullRedTerm′ (zero-refl ⊢Γ) = zero , zeroₙ , refl (zeroⱼ ⊢Γ)
  fullRedTerm′ (suc-cong t) =
    let u , nf , t≡u = fullRedTerm t
    in  suc u , sucₙ nf , suc-cong t≡u
  fullRedTerm′ (η-eq ⊢F ⊢t _ _ _ t∘0) =
    let u , nf , t∘0≡u = fullRedTerm t∘0
        _ , _ , ⊢u = syntacticEqTerm t∘0≡u
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        λu∘0 = lam (U.wk (lift (step id)) u) ∘ var 0
    in  lam u , lamₙ nf
     ,  η-eq ⊢F ⊢t (lamⱼ ⊢F ⊢u)
             (trans t∘0≡u (PE.subst₂ (λ x y → _ ⊢ x ≡ λu∘0 ∷ y)
                                     (wkSingleSubstId u) (wkSingleSubstId _)
                                     (sym (β-red wk⊢F wk⊢u (var ΓF⊢ here)))))
