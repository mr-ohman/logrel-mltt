{-# OPTIONS --without-K #-}

module Definition.Typed.Properties where

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Tools.Nat
import Tools.PropositionalEquality as PE


-- Wellformed context extraction

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕ ⊢Γ) = ⊢Γ
wfTerm (Π F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lam F t) with wfTerm t
wfTerm (lam F t) | ⊢Γ ∙ F' = ⊢Γ
wfTerm (g ∘ a) = wfTerm a
wfTerm (zero ⊢Γ) = ⊢Γ
wfTerm (suc n) = wfTerm n
wfTerm (natrec F z s n) = wfTerm z
wfTerm (conv t A≡B) = wfTerm t

wf : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wf (ℕ ⊢Γ) = ⊢Γ
wf (U ⊢Γ) = ⊢Γ
wf (Π F ▹ G) = wf F
wf (univ A) = wfTerm A

wfEqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a) = wfTerm a
wfEqTerm (fun-ext F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong F≡F' z≡z' s≡s' n≡n') = wfEqTerm z≡z'
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n

wfEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wfEq F≡H


-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n') =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n')
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (app-subst t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t a) = β-red A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t' ⇨ t⇒*u) = trans (subsetTerm t⇒t') (subset*Term t⇒*u)

subset* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A' ⇨ A'⇒*B) = trans (subset A⇒A') (subset* A'⇒*B)


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ a
redFirstTerm (β-red A t a) = (lam A t) ∘ a
redFirstTerm (natrec-subst F z s n⇒n') = natrec F z s (redFirstTerm n⇒n')
redFirstTerm (natrec-zero F z s) = natrec F z s (zero (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrec F z s (suc n)

redFirst : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t' ⇨ t'⇒*u) = redFirstTerm t⇒t'

redFirst* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A' ⇨ A'⇒*B) = redFirst A⇒A'


-- No neutral terms are well-formed in an empty context

noNe : ∀ {t A} → ε ⊢ t ∷ A → Neutral t → ⊥
noNe (var x₁ ()) (var x)
noNe (conv ⊢t x) (var n) = noNe ⊢t (var n)
noNe (⊢t ∘ ⊢t₁) (_∘_ neT) = noNe ⊢t neT
noNe (conv ⊢t x) (_∘_ neT) = noNe ⊢t (_∘_ neT)
noNe (natrec x ⊢t ⊢t₁ ⊢t₂) (natrec neT) = noNe ⊢t₂ neT
noNe (conv ⊢t x) (natrec neT) = noNe ⊢t (natrec neT)

-- Neutrals do not weak head reduce

neRedTerm : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (_∘_ n) = neRedTerm d n
neRedTerm (β-red x x₁ x₂) (_∘_ ())
neRedTerm (natrec-subst x x₁ x₂ d) (natrec n₁) = neRedTerm d n₁
neRedTerm (natrec-zero x x₁ x₂) (natrec ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrec ())

neRed : ∀ {Γ A B} (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce

whnfRedTerm : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (_∘_ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red x x₁ x₂) (ne (_∘_ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrec x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrec ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrec ()))

whnfRed : ∀ {Γ A B} (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : ∀ {Γ t u A} (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) U = PE.refl
whnfRed*Term (id x) Π = PE.refl
whnfRed*Term (id x) ℕ = PE.refl
whnfRed*Term (id x) lam = PE.refl
whnfRed*Term (id x) zero = PE.refl
whnfRed*Term (id x) suc = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)

whnfRed* : ∀ {Γ A B} (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic

whrDetTerm : ∀{Γ t u A u' A'} (d : Γ ⊢ t ⇒ u ∷ A) (d' : Γ ⊢ t ⇒ u' ∷ A') → u PE.≡ u'
whrDetTerm (conv d x) d' = whrDetTerm d d'
whrDetTerm d (conv d' x₁) = whrDetTerm d d'
whrDetTerm (app-subst d x) (app-subst d' x₁) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lam)
whrDetTerm (β-red x x₁ x₂) (app-subst d x₃) = ⊥-elim (whnfRedTerm d lam)
whrDetTerm (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zero)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d suc)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d') = ⊥-elim (whnfRedTerm d' zero)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d') = ⊥-elim (whnfRedTerm d' suc)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl

whrDet : ∀{Γ A B B'} (d : Γ ⊢ A ⇒ B) (d' : Γ ⊢ A ⇒ B') → B PE.≡ B'
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : ∀{Γ t u A u'} (d : Γ ⊢ t ↘ u ∷ A) (d' : Γ ⊢ t ⇒* u' ∷ A) → Γ ⊢ u' ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d') = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d') =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d'

whrDet*Term : ∀{Γ t u A u'} (d : Γ ⊢ t ↘ u ∷ A) (d' : Γ ⊢ t ↘ u' ∷ A) → u PE.≡ u'
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : ∀{Γ A B B'} (d : Γ ⊢ A ↘ B) (d' : Γ ⊢ A ↘ B') → B PE.≡ B'
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A' ⇨ A'⇒*B , whnfB) (A⇒A'' ⇨ A''⇒*B' , whnfB') =
  whrDet* (A'⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (whrDet A⇒A'' A⇒A')
                                     (A''⇒*B' , whnfB'))

-- Identity of syntactic reduction

idRed:*: : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : ∀ {A Γ} → Γ ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : ∀ {A B t a Γ}
         → t [ a ] PE.≡ U
         → Γ ⊢ a ∷ A
         → Γ ∙ A ⊢ t ∷ B
         → ⊥
UnotInA[t] () x₁ (ℕ x₂)
UnotInA[t] () x₁ (Π x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lam x₂ x₃)
UnotInA[t] () x₁ (x₂ ∘ x₃)
UnotInA[t] () x₁ (zero x₂)
UnotInA[t] () x₁ (suc x₂)
UnotInA[t] () x₁ (natrec x₂ x₃ x₄ x₅)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term' : ∀ {A B U' Γ} → U' PE.≡ U → Γ ⊢ A ⇒ U' ∷ B → ⊥
redU*Term' U'≡U (conv A⇒U x) = redU*Term' U'≡U A⇒U
redU*Term' () (app-subst A⇒U x)
redU*Term' U'≡U (β-red x x₁ x₂) = UnotInA[t] U'≡U x₂ x₁
redU*Term' () (natrec-subst x x₁ x₂ A⇒U)
redU*Term' U'≡U (natrec-zero x x₁ x₂) rewrite U'≡U = UnotInA x₁
redU*Term' () (natrec-suc x x₁ x₂ x₃)

redU*Term : ∀ {A B Γ} → Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : ∀ {A Γ} → Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term' PE.refl x

redU* : ∀ {A Γ} → Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)
