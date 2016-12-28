module Definition.Conversion.Lift where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
import Definition.LogicalRelation.Consequences.Inequality as WF
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Substitution
open import Definition.LogicalRelation.Consequences.SingleSubst

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


mutual
  ne~↑ : ∀ {t u A Γ}
       → Γ ⊢ t ~ u ↑ A
       → Neutral t × Neutral u
  ne~↑ (var x₁) = var _ , var _
  ne~↑ (app x x₁) = let q , w = ne~↓ x
                    in  _∘_ q , _∘_ w
  ne~↑ (natrec x x₁ x₂ x₃) = let q , w = ne~↓ x₃
                             in  natrec q , natrec w

  ne~↓ : ∀ {t u A Γ}
       → Γ ⊢ t ~ u ↓ A
       → Neutral t × Neutral u
  ne~↓ ([~] A₁ D whnfB k~l) = ne~↑ k~l

whnfConv↓ : ∀ {A B Γ}
          → Γ ⊢ A [conv↓] B
          → Whnf A × Whnf B
whnfConv↓ (U-refl x) = U , U
whnfConv↓ (ℕ-refl x) = ℕ , ℕ
whnfConv↓ (ne x) = let neA , neB = ne~↓ x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong x x₁ x₂) = Π , Π

whnfConv↓Term : ∀ {t u A Γ}
              → Γ ⊢ t [conv↓] u ∷ A
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x x₁) = let neT , neU = ne~↑ x
                             in ℕ , ne neT , ne neU
whnfConv↓Term (ne-ins x x₁ x₂) = let neT , neU = ne~↑ x
                                 in ne x₂ , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = U , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕ , zero , zero
whnfConv↓Term (suc-cong x) = ℕ , suc , suc
whnfConv↓Term (fun-ext x x₁ x₂ y y₁ x₃) = Π , y , y₁

liftConv : ∀ {A B Γ}
          → Γ ⊢ A [conv↓] B
          → Γ ⊢ A [conv↑] B
liftConv A<>B =
  let ⊢A , ⊢B = syntacticEq (soundnessConv↓ A<>B)
      whnfA , whnfB = whnfConv↓ A<>B
  in  [↑] _ _ (id ⊢A) (id ⊢B) whnfA whnfB A<>B

liftConvTerm : ∀ {t u A Γ}
             → Γ ⊢ t [conv↓] u ∷ A
             → Γ ⊢ t [conv↑] u ∷ A
liftConvTerm t<>u =
  let ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundnessConv↓Term t<>u)
      whnfA , whnfT , whnfU = whnfConv↓Term t<>u
  in  [↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢u) whnfA whnfT whnfU t<>u
