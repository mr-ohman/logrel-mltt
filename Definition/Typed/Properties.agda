module Definition.Typed.Properties where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product

open import Tools.Context
open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties using (wkIndex-step; wkIndex-lift; wk-β; wk-β-natrec)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)
import Relation.Binary.PropositionalEquality as PE


-- Wellformed context extraction

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕ x) = x
wfTerm (Π x ▹ x₁) = wfTerm x
wfTerm (var x x₁) = x
wfTerm (lam x x₁) with wfTerm x₁
wfTerm (lam x₁ x₂) | q ∙ x = q
wfTerm (x ∘ x₁) = wfTerm x₁
wfTerm (zero x) = x
wfTerm (suc x) = wfTerm x
wfTerm (natrec x x₁ x₂ x₃) = wfTerm x₁
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
wfEqTerm (Π-cong x x₁ x₂) = wfEqTerm x₁
wfEqTerm (app-cong x x₁) = wfEqTerm x
wfEqTerm (β-red x x₁ x₂) = wfTerm x₂
wfEqTerm (fun-ext x x₁ x₂ x₃) = wfTerm x₁
wfEqTerm (suc-cong x) = wfEqTerm x
wfEqTerm (natrec-cong x x₁ x₂ x₃) = wfEqTerm x₂
wfEqTerm (natrec-zero x x₁ x₂) = wfTerm x₁
wfEqTerm (natrec-suc x x₁ x₂ x₃) = wfTerm x

wfEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ x) = wfEqTerm x
wfEq (refl x) = wf x
wfEq (sym x) = wfEq x
wfEq (trans x x₁) = wfEq x
wfEq (Π-cong x x₁ x₂) = wfEq x₁


-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst x x₁ x₂ x₃) = natrec-cong (refl x) (refl x₁) (refl x₂) (subsetTerm x₃)
subsetTerm (natrec-zero x x₁ x₂) = natrec-zero x x₁ x₂
subsetTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc x x₁ x₂ x₃
subsetTerm (app-subst x x₁) = app-cong (subsetTerm x) (refl x₁)
subsetTerm (β-red x x₁ x₂) = β-red x x₁ x₂
subsetTerm (conv x x₁) = conv (subsetTerm x) x₁

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ x) = univ (subsetTerm x)

subset*Term : ∀ {Γ A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (x ⇨ x₁) = trans (subsetTerm x) (subset*Term x₁)

subset* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (x ⇨ x₁) = trans (subset x) (subset* x₁)


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv d x) = conv (redFirstTerm d) x
redFirstTerm (app-subst d x) = (redFirstTerm d) ∘ x
redFirstTerm (β-red x x₁ x₂) = (lam x x₁) ∘ x₂
redFirstTerm (natrec-subst x x₁ x₂ d) = natrec x x₁ x₂ (redFirstTerm d)
redFirstTerm (natrec-zero x x₁ x₂) = natrec x x₁ x₂ (zero (wfTerm x₁))
redFirstTerm (natrec-suc x x₁ x₂ x₃) = natrec x₁ x₂ x₃ (suc x)

redFirst : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ x) = univ (redFirstTerm x)

redFirst*Term : ∀ {Γ t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id x) = x
redFirst*Term (x ⇨ d) = redFirstTerm x

redFirst* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id x) = x
redFirst* (x ⇨ x₁) = redFirst x


-- Neutrals do not weak head reduce

neRed :   ∀{Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRed (conv d x) n = neRed d n
neRed (app-subst d x) (_∘_ n) = neRed d n
neRed (β-red x x₁ x₂) (_∘_ ())
neRed (natrec-subst x x₁ x₂ d) (natrec n₁) = neRed d n₁
neRed (natrec-zero x x₁ x₂) (natrec ())
neRed (natrec-suc x x₁ x₂ x₃) (natrec ())

-- Whnfs do not weak head reduce

whnfRed :  ∀{Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRed (conv d x) w = whnfRed d w
whnfRed (app-subst d x) (ne (_∘_ x₁)) = neRed d x₁
whnfRed (β-red x x₁ x₂) (ne (_∘_ ()))
whnfRed (natrec-subst x x₁ x₂ d) (ne (natrec x₃)) = neRed d x₃
whnfRed (natrec-zero x x₁ x₂) (ne (natrec ()))
whnfRed (natrec-suc x x₁ x₂ x₃) (ne (natrec ()))

whnfRed' : ∀{Γ A B} (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed' (univ x) w = whnfRed x w

whnfRed* : ∀{Γ t u A} (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed* (id x) U = PE.refl
whnfRed* (id x) Π = PE.refl
whnfRed* (id x) ℕ = PE.refl
whnfRed* (id x) lam = PE.refl
whnfRed* (id x) zero = PE.refl
whnfRed* (id x) suc = PE.refl
whnfRed* (id x) (ne x₁) = PE.refl
whnfRed* (conv x x₁ ⇨ d) w = ⊥-elim (whnfRed x w)
whnfRed* (x ⇨ d) (ne x₁) = ⊥-elim (neRed x x₁)

whnfRed*' : ∀{Γ A B} (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
whnfRed*' (id x) w = PE.refl
whnfRed*' (x ⇨ d) w = ⊥-elim (whnfRed' x w)

-- Whr is deterministic

whrDet : ∀{Γ t u A u' A'} (d : Γ ⊢ t ⇒ u ∷ A) (d' : Γ ⊢ t ⇒ u' ∷ A') → u PE.≡ u'
whrDet (conv d x) d' = whrDet d d'
whrDet d (conv d' x₁) = whrDet d d'
whrDet (app-subst d x) (app-subst d' x₁) rewrite whrDet d d' = PE.refl
whrDet (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRed d lam)
whrDet (β-red x x₁ x₂) (app-subst d x₃) = ⊥-elim (whnfRed d lam)
whrDet (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
whrDet (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d') rewrite whrDet d d' = PE.refl
whrDet (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRed d zero)
whrDet (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRed d suc)
whrDet (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d') = ⊥-elim (whnfRed d' zero)
whrDet (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDet (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d') = ⊥-elim (whnfRed d' suc)
whrDet (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl

whrDet' : ∀{Γ A B B'} (d : Γ ⊢ A ⇒ B) (d' : Γ ⊢ A ⇒ B') → B PE.≡ B'
whrDet' (univ x) (univ x₁) = whrDet x x₁

whrDet↘ : ∀{Γ t u A u'} (d : Γ ⊢ t ↘ u ∷ A) (d' : Γ ⊢ t ⇒* u' ∷ A) → Γ ⊢ u' ⇒* u ∷ A
whrDet↘ (proj₁ , proj₂) (id x) = proj₁
whrDet↘ (id x , proj₂) (x₁ ⇨ d') = ⊥-elim (whnfRed x₁ proj₂)
whrDet↘ (x ⇨ proj₁ , proj₂) (x₁ ⇨ d') = whrDet↘ (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDet x x₁) (proj₁ , proj₂)) d'

whrDet* : ∀{Γ t u A u'} (d : Γ ⊢ t ↘ u ∷ A) (d' : Γ ⊢ t ↘ u' ∷ A) → u PE.≡ u'
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) = whrDet* (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDet x₁ x) (proj₃ , proj₄))

whrDet*' : ∀{Γ A B B'} (d : Γ ⊢ A ↘ B) (d' : Γ ⊢ A ↘ B') → B PE.≡ B'
whrDet*' (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*' (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed' x₁ proj₂)
whrDet*' (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed' x proj₄)
whrDet*' (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) = whrDet*' (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _) (whrDet' x₁ x) (proj₃ , proj₄))

U≢ℕ : Term.U PE.≢ ℕ
U≢ℕ ()

U≢Π : ∀ {F G} → Term.U PE.≢ Π F ▹ G
U≢Π ()

U≢ne : ∀ {K} → Neutral K → U PE.≢ K
U≢ne () PE.refl

ℕ≢Π : ∀ {F G} → Term.ℕ PE.≢ Π F ▹ G
ℕ≢Π ()

ℕ≢ne : ∀ {K} → Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

Π≢ne : ∀ {F G K} → Neutral K → Π F ▹ G PE.≢ K
Π≢ne () PE.refl

Π-PE-injectivity : ∀ {F G H E} → Term.Π F ▹ G PE.≡ Π H ▹ E → F PE.≡ H × G PE.≡ E
Π-PE-injectivity PE.refl = PE.refl , PE.refl

idRed:*: : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- Properties of U

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

redUTerm : ∀ {A B U' Γ} → U' PE.≡ U → Γ ⊢ A ⇒ U' ∷ B → ⊥
redUTerm U'≡U (conv A⇒U x) = redUTerm U'≡U A⇒U
redUTerm () (app-subst A⇒U x)
redUTerm U'≡U (β-red x x₁ x₂) = UnotInA[t] U'≡U x₂ x₁
redUTerm () (natrec-subst x x₁ x₂ A⇒U)
redUTerm U'≡U (natrec-zero x x₁ x₂) rewrite U'≡U = UnotInA x₁
redUTerm () (natrec-suc x x₁ x₂ x₃)

redU*Term : ∀ {A B Γ} → Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

redU : ∀ {A Γ} → Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redUTerm PE.refl x

redU* : ∀ {A Γ} → Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)
