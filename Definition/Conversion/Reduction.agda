module Definition.Conversion.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion


reductionConv↑ : ∀ {A A' B B' Γ}
               → Γ ⊢ A ⇒* A'
               → Γ ⊢ B ⇒* B'
               → Whnf A'
               → Whnf B'
               → Γ ⊢ A' [conv↑] B'
               → Γ ⊢ A  [conv↑] B
reductionConv↑ x x₁ x₂ x₃ ([↑] A'' B'' D D' whnfA' whnfB' A'<>B')
              rewrite whnfRed*' D x₂ | whnfRed*' D' x₃ =
  [↑] A'' B'' x x₁ whnfA' whnfB' A'<>B'

reductionConv↑Term : ∀ {t t' u u' A B Γ}
                   → Γ ⊢ A ⇒* B
                   → Γ ⊢ t ⇒* t' ∷ B
                   → Γ ⊢ u ⇒* u' ∷ B
                   → Whnf B
                   → Whnf t'
                   → Whnf u'
                   → Γ ⊢ t' [conv↑] u' ∷ B
                   → Γ ⊢ t  [conv↑] u  ∷ A
reductionConv↑Term x x₁ x₂ x₃ x₄ x₅
                   ([↑]ₜ B₁ t'' u'' D d d' whnfB whnft' whnfu' t<>u)
                   rewrite whnfRed*' D x₃ | whnfRed* d x₄ | whnfRed* d' x₅ =
  [↑]ₜ B₁ t'' u'' x x₁ x₂ whnfB whnft' whnfu' t<>u
