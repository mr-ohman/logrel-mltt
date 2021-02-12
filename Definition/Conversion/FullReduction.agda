{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.FullReduction where

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.Substitution

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m : Nat
    Γ : Con Term m
    A B C : Term m
    c g k n p u : Term m

mutual
  data NfNeutral {m : Nat} : Term m → Set where
    var       : (x : Fin m)                             → NfNeutral (var x)
    ∘ₙ        : {k u : Term m}     → NfNeutral k → Nf u → NfNeutral (k ∘ u)
    fstₙ      : {p : Term m}       → NfNeutral p        → NfNeutral (fst p)
    sndₙ      : {p : Term m}       → NfNeutral p        → NfNeutral (snd p)
    natrecₙ   : {C : Term (1+ m)} {c g k : Term m}
                     → Nf C → Nf c → Nf g → NfNeutral k → NfNeutral (natrec C c g k)
    Emptyrecₙ : {C k : Term m}     → Nf C → NfNeutral k → NfNeutral (Emptyrec C k)

  data Nf {m : Nat} : Term m → Set where
    Uₙ     : Nf U
    Πₙ     : {A : Term m} {B : Term (1+ m)} → Nf A → Nf B → Nf (Π A ▹ B)
    Σₙ     : {A : Term m} {B : Term (1+ m)} → Nf A → Nf B → Nf (Σ A ▹ B)
    ℕₙ     : Nf ℕ
    Emptyₙ : Nf Empty
    Unitₙ  : Nf Unit

    lamₙ   : {t : Term (1+ m)} → Nf t → Nf (lam t)
    prodₙ  : {t u : Term m} → Nf t → Nf u → Nf (prod t u)
    zeroₙ  : Nf zero
    sucₙ   : {t : Term m} → Nf t → Nf (suc t)
    starₙ  : Nf star

    ne     : {n : Term m} → NfNeutral n → Nf n


mutual
  fullRedNe : ∀ {t A} → Γ ⊢ t ~ t ↑ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe (var-refl x _) = var _ , var _ , refl x
  fullRedNe (app-cong t u) =
    let t′ , nfT′ , t≡t′ = fullRedNe~↓ t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in  (t′ ∘ u′) , (∘ₙ nfT′ nfU′) , app-cong t≡t′ u≡u′
  fullRedNe (fst-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst p′ , fstₙ neP′ , fst-cong ⊢F ⊢G p≡p′
  fullRedNe (snd-cong p~p) =
    let p′ , neP′ , p≡p′ = fullRedNe~↓ p~p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd p′ , sndₙ neP′ , snd-cong ⊢F ⊢G p≡p′
  fullRedNe (natrec-cong C z s n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        z′ , nfZ′ , z≡z′ = fullRedTerm z
        s′ , nfS′ , s≡s′ = fullRedTerm s
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  natrec C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
     ,  natrec-cong C≡C′ z≡z′ s≡s′ n≡n′
  fullRedNe (Emptyrec-cong C n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        n′ , nfN′ , n≡n′ = fullRedNe~↓ n
    in  Emptyrec C′ n′ , Emptyrecₙ nfC′ nfN′
     ,  Emptyrec-cong C≡C′ n≡n′

  fullRedNe~↓ : ∀ {t A} → Γ ⊢ t ~ t ↓ A → ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A
  fullRedNe~↓ ([~] A D whnfB k~l) =
    let u , nf , t≡u = fullRedNe k~l
    in  u , nf , conv t≡u (subset* D)

  fullRed : ∀ {A} → Γ ⊢ A [conv↑] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRed ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
    rewrite whrDet* (D , whnfA′) (D′ , whnfB′) =
    let B″ , nf , B′≡B″ = fullRedConv↓ A′<>B′
    in  B″ , nf , trans (subset* D′) B′≡B″

  fullRedConv↓ : ∀ {A} → Γ ⊢ A [conv↓] A → ∃ λ B → Nf B × Γ ⊢ A ≡ B
  fullRedConv↓ (U-refl ⊢Γ) = U , Uₙ , refl (Uⱼ ⊢Γ)
  fullRedConv↓ (ℕ-refl ⊢Γ) = ℕ , ℕₙ , refl (ℕⱼ ⊢Γ)
  fullRedConv↓ (Empty-refl ⊢Γ) = Empty , Emptyₙ , refl (Emptyⱼ ⊢Γ)
  fullRedConv↓ (Unit-refl ⊢Γ) = Unit , Unitₙ , refl (Unitⱼ ⊢Γ)
  fullRedConv↓ (ne A) =
    let B , nf , A≡B = fullRedNe~↓ A
    in  B , ne nf , univ A≡B
  fullRedConv↓ (Π-cong ⊢F F G) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  Π F′ ▹ G′ , Πₙ nfF′ nfG′ , Π-cong ⊢F F≡F′ G≡G′
  fullRedConv↓ (Σ-cong ⊢F F G) =
    let F′ , nfF′ , F≡F′ = fullRed F
        G′ , nfG′ , G≡G′ = fullRed G
    in  Σ F′ ▹ G′ , Σₙ nfF′ nfG′ , Σ-cong ⊢F F≡F′ G≡G′

  fullRedTerm : ∀ {t A} → Γ ⊢ t [conv↑] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTerm ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
    rewrite whrDet*Term (d , whnft′) (d′ , whnfu′) =
    let u″ , nf , u′≡u″ = fullRedTermConv↓ t<>u
    in  u″ , nf , conv (trans (subset*Term d′) u′≡u″) (sym (subset* D))

  fullRedTermConv↓ : ∀ {t A} → Γ ⊢ t [conv↓] t ∷ A → ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A
  fullRedTermConv↓ (ℕ-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (Empty-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (Unit-ins t) =
    let u , nf , t≡u = fullRedNe~↓ t
    in  u , ne nf , t≡u
  fullRedTermConv↓ (ne-ins ⊢t _ _ t) =
    let u , nfU , t≡u = fullRedNe~↓ t
        _ , ⊢t∷M , _ = syntacticEqTerm t≡u
        _ , neT , _ = ne~↓ t
    in  u , ne nfU , conv t≡u (neTypeEq neT ⊢t∷M ⊢t)
  fullRedTermConv↓ (univ ⊢t _ t) =
    let u , nf , t≡u = fullRedConv↓ t
    in  u , nf , inverseUnivEq ⊢t t≡u
  fullRedTermConv↓ (zero-refl ⊢Γ) = zero , zeroₙ , refl (zeroⱼ ⊢Γ)
  fullRedTermConv↓ (suc-cong t) =
    let u , nf , t≡u = fullRedTerm t
    in  suc u , sucₙ nf , suc-cong t≡u
  fullRedTermConv↓ (η-eq ⊢t _ _ _ t∘0) =
    let u , nf , t∘0≡u = fullRedTerm t∘0
        _ , _ , ⊢u = syntacticEqTerm t∘0≡u
        ⊢F , _ = syntacticΠ (syntacticTerm ⊢t)
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        λu∘0 = lam (U.wk (lift (step id)) u) ∘ var x0
    in  lam u , lamₙ nf
     ,  η-eq ⊢F ⊢t (lamⱼ ⊢F ⊢u)
                (trans t∘0≡u (PE.subst₂ (λ x y → _ ⊢ x ≡ λu∘0 ∷ y)
                                        (wkSingleSubstId u) (wkSingleSubstId _)
                                        (sym (β-red wk⊢F wk⊢u (var ΓF⊢ here)))))
  fullRedTermConv↓ (Σ-η ⊢t _ tProd _ fstConv sndConv) =
    let fst′ , nfFst′ , fst≡fst′ = fullRedTerm fstConv
        snd′ , nfSnd′ , snd≡snd′ = fullRedTerm sndConv
        _ , _ , ⊢fst′ = syntacticEqTerm fst≡fst′
        _ , _ , ⊢snd′₁ = syntacticEqTerm snd≡snd′
        ⊢ΣFG = syntacticTerm ⊢t
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG

        Gfst≡Gfst′ = substTypeEq (refl ⊢G) fst≡fst′
        ⊢snd′ = conv ⊢snd′₁ Gfst≡Gfst′
        ⊢prod = prodⱼ ⊢F ⊢G ⊢fst′ ⊢snd′

        fstprod≡fst′ = Σ-β₁ ⊢F ⊢G ⊢fst′ ⊢snd′
        fst≡fstprod = trans fst≡fst′ (sym fstprod≡fst′)
        Gfst≡Gfstprod = substTypeEq (refl ⊢G) fst≡fstprod
        sndprod≡snd′ = conv (Σ-β₂ ⊢F ⊢G ⊢fst′ ⊢snd′) (sym Gfst≡Gfstprod)
        snd≡sndprod = trans snd≡snd′ (sym sndprod≡snd′)
    in  prod fst′ snd′ , prodₙ nfFst′ nfSnd′
      , Σ-η ⊢F ⊢G ⊢t ⊢prod fst≡fstprod snd≡sndprod
  fullRedTermConv↓ (η-unit ⊢t _ tUnit _) =
    star , starₙ , η-unit ⊢t (starⱼ (wfTerm ⊢t))
