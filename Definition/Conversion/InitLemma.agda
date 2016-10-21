module Definition.Conversion.InitLemma where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps

open import Data.Product


lemma2 : ∀ {a A Γ} → Γ ⊢ A → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a ⇒* b ∷ A
lemma2 A (ℕ x) = ℕ , ℕ , id (ℕ x)
lemma2 A (Π a ▹ a₁) = Π _ ▹ _ , Π , id (Π a ▹ a₁)
lemma2 A (var x₁ x₂) = var _ , ne (var _) , id (var x₁ x₂)
lemma2 A (lam x a) = lam _ , lam , id (lam x a)
lemma2 A (a₁ ∘ a₂) = {!!}
lemma2 A (zero x) = zero , zero , id (zero x)
lemma2 A (suc a) = suc _ , suc , id (suc a)
lemma2 A (natrec x a a₁ a₂) = {!!} , {!!} , {!!}
lemma2 A (conv a₁ x) = let a , b , c = lemma2 {!!} a₁
                       in  a , b , conv* c x

lemma1 : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
lemma1 (ℕ x) = ℕ , ℕ , id (ℕ x)
lemma1 (U x) = U , U , id (U x)
lemma1 (Π A ▹ A₁) = Π _ ▹ _ , Π , id (Π A ▹ A₁)
lemma1 (univ x) = let a , b , c = lemma2 (U (wfTerm x)) x
                  in  a , b , univ* c

lem4 : ∀ {x A B Γ} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
lem4 A B here here = refl A
lem4 A B (there a) (there b) = let q = lem4 {!!} {!!} a b
                               in  wkEq (step id) ({!!} ∙ {!!}) q

lemma3 : ∀ {t A B Γ} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
lemma3 (var x) (var x₁ x₂) (var x₃ x₄) = {!!}
lemma3 (var x) t∷A (conv t∷B x₃) = let q = lemma3 (var x) t∷A t∷B
                                   in  trans q x₃
lemma3 (var x) (conv t∷A x₁) t∷B = let q = lemma3 (var x) t∷A t∷B
                                   in  trans (sym x₁) q
lemma3 (_∘_ neT) t∷A t∷B = {!!}
lemma3 (natrec neT) t∷A t∷B = {!!}

lemma4 : ∀ {v k R T Γ}
       → Neutral k → Γ ⊢ v ∷ R → Γ ⊢ v ∷ T → Γ ⊢ v ⇒ k ∷ R
       → Γ ⊢ T ≡ R
lemma4 = {!!}
