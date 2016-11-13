module Definition.Typed.Properties where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
     using (wkIndex-step; wkIndex-lift; wk-β; wk-β-natrec)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)
import Relation.Binary.PropositionalEquality as PE


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


-- Neutrals do not weak head reduce

neRed : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRed (conv d x) n = neRed d n
neRed (app-subst d x) (_∘_ n) = neRed d n
neRed (β-red x x₁ x₂) (_∘_ ())
neRed (natrec-subst x x₁ x₂ d) (natrec n₁) = neRed d n₁
neRed (natrec-zero x x₁ x₂) (natrec ())
neRed (natrec-suc x x₁ x₂ x₃) (natrec ())

-- Whnfs do not weak head reduce

whnfRed : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRed (conv d x) w = whnfRed d w
whnfRed (app-subst d x) (ne (_∘_ x₁)) = neRed d x₁
whnfRed (β-red x x₁ x₂) (ne (_∘_ ()))
whnfRed (natrec-subst x x₁ x₂ d) (ne (natrec x₃)) = neRed d x₃
whnfRed (natrec-zero x x₁ x₂) (ne (natrec ()))
whnfRed (natrec-suc x x₁ x₂ x₃) (ne (natrec ()))

whnfRed' : ∀ {Γ A B} (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed' (univ x) w = whnfRed x w

whnfRed* : ∀ {Γ t u A} (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed* (id x) U = PE.refl
whnfRed* (id x) Π = PE.refl
whnfRed* (id x) ℕ = PE.refl
whnfRed* (id x) lam = PE.refl
whnfRed* (id x) zero = PE.refl
whnfRed* (id x) suc = PE.refl
whnfRed* (id x) (ne x₁) = PE.refl
whnfRed* (conv x x₁ ⇨ d) w = ⊥-elim (whnfRed x w)
whnfRed* (x ⇨ d) (ne x₁) = ⊥-elim (neRed x x₁)

whnfRed*' : ∀ {Γ A B} (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
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
whrDet↘ (x ⇨ proj₁ , proj₂) (x₁ ⇨ d') =
  whrDet↘ (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDet x x₁) (proj₁ , proj₂)) d'

whrDet* : ∀{Γ t u A u'} (d : Γ ⊢ t ↘ u ∷ A) (d' : Γ ⊢ t ↘ u' ∷ A) → u PE.≡ u'
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet* (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDet x₁ x) (proj₃ , proj₄))

whrDet*' : ∀{Γ A B B'} (d : Γ ⊢ A ↘ B) (d' : Γ ⊢ A ↘ B') → B PE.≡ B'
whrDet*' (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*' (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed' x₁ proj₂)
whrDet*' (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed' x proj₄)
whrDet*' (A⇒A' ⇨ A'⇒*B , whnfB) (A⇒A'' ⇨ A''⇒*B' , whnfB') =
  whrDet*' (A'⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (whrDet' A⇒A'' A⇒A')
                                     (A''⇒*B' , whnfB'))

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

zero≢suc : ∀ {n} → Term.zero PE.≢ suc n
zero≢suc ()

zero≢ne : ∀ {k} → Neutral k → Term.zero PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → Term.suc n PE.≢ k
suc≢ne () PE.refl

Π-PE-injectivity : ∀ {F G H E} → Term.Π F ▹ G PE.≡ Π H ▹ E → F PE.≡ H × G PE.≡ E
Π-PE-injectivity PE.refl = PE.refl , PE.refl

suc-PE-injectivity : ∀ {n m} → Term.suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl

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
