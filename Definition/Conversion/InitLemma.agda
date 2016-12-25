{-# OPTIONS --without-K #-}

module Definition.Conversion.InitLemma where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.SingleSubst
open import Definition.LogicalRelation.Consequences.Inversion
import Definition.LogicalRelation.Consequences.Inequality as WF

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
open import Tools.Nullary
import Tools.PropositionalEquality as PE


natrec-subst* : ∀ {Γ F z s n n'} → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
              → Γ ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
              → Γ ⊢ n ⇒* n' ∷ ℕ
              → Γ ⊢ natrec F z s n ⇒* natrec F z s n' ∷ F [ n ]
natrec-subst* F z s (id x) = id (natrec F z s x)
natrec-subst* F z s (x ⇨ y) =
  (natrec-subst F z s x) ⇨
  (conv* (natrec-subst* F z s y)
         (sym (substTypeEq (refl F) (subsetTerm x))))

lemma2 : ∀ {a A Γ} → Γ ⊢ A → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a ⇒* b ∷ A
lemma2 A (ℕ x) = ℕ , ℕ , id (ℕ x)
lemma2 A (Π a ▹ a₁) = Π _ ▹ _ , Π , id (Π a ▹ a₁)
lemma2 A (var x₁ x₂) = var _ , ne (var _) , id (var x₁ x₂)
lemma2 A (lam x a) = lam _ , lam , id (lam x a)
lemma2 A (a₁ ∘ a₂) with lemma2 (syntacticTerm a₁) a₁
lemma2 A (a₁ ∘ a₂) | .U , U , proj₃ =
  let _ , _ , q = syntacticRedTerm proj₃
  in  ⊥-elim (UnotInA q)
lemma2 A₁ (a₁ ∘ a₂) | _ , Π , proj₃ =
  let _ , _ , Π∷Π = syntacticRedTerm proj₃
      Π≡U = inversion-Π Π∷Π
  in  ⊥-elim (WF.U≢Π (sym Π≡U))
lemma2 A (a₁ ∘ a₂) | .ℕ , ℕ , proj₃ =
  let _ , _ , ℕ∷Π = syntacticRedTerm proj₃
      Π≡U = inversion-ℕ ℕ∷Π
  in  ⊥-elim (WF.U≢Π (sym Π≡U))
lemma2 A (a₁ ∘ a₂) | _ , lam , red =
  let _ , _ , y = syntacticRedTerm red
      _ , _ , r , t = inversion-lam y
      q , w , e = lemma2 {!!} {!!}
  in  q , w , (app-subst* red a₂ ⇨∷* (β-red (syntacticTerm a₂) {!!} a₂ ⇨ e))
lemma2 A (a₁ ∘ a₂) | .zero , zero , proj₃ =
  let _ , _ , zero∷Π = syntacticRedTerm proj₃
      Π≡ℕ = inversion-zero zero∷Π
  in  ⊥-elim (WF.ℕ≢Π (sym Π≡ℕ))
lemma2 A (a₁ ∘ a₂) | _ , suc , proj₃ =
  let _ , _ , suc∷Π = syntacticRedTerm proj₃
      Π≡ℕ = inversion-suc suc∷Π
  in  ⊥-elim (WF.ℕ≢Π (sym Π≡ℕ))
lemma2 A (a₁ ∘ a₂) | n , ne x , red = _ , ne (_∘_ x) , app-subst* red a₂
lemma2 A (zero x) = zero , zero , id (zero x)
lemma2 A (suc a) = suc _ , suc , id (suc a)
lemma2 A (natrec x a a₁ a₂) with lemma2 (syntacticTerm a₂) a₂
lemma2 A (natrec x a a₁ a₂) | .U , U , proj₃ =
  let _ , _ , q = syntacticRedTerm proj₃
  in  ⊥-elim (UnotInA q)
lemma2 A₁ (natrec x a a₁ a₂) | _ , Π , proj₃ =
  let _ , _ , Π∷ℕ = syntacticRedTerm proj₃
      ℕ≡U = inversion-Π Π∷ℕ
  in  ⊥-elim (WF.U≢ℕ (sym ℕ≡U))
lemma2 A (natrec x a a₁ a₂) | .ℕ , ℕ , proj₃ =
  let _ , _ , ℕ∷ℕ = syntacticRedTerm proj₃
      ℕ≡U = inversion-ℕ ℕ∷ℕ
  in  ⊥-elim (WF.U≢ℕ (sym ℕ≡U))
lemma2 A (natrec x a a₁ a₂) | _ , lam , proj₃ =
  let _ , _ , lam∷ℕ = syntacticRedTerm proj₃
      _ , _ , _ , ℕ≡Π = inversion-lam lam∷ℕ
  in  ⊥-elim (WF.ℕ≢Π ℕ≡Π)
lemma2 A (natrec x a a₁ a₂) | .zero , zero , proj₃ = {!!}
lemma2 A (natrec x a a₁ a₂) | _ , suc , proj₃ = {!!}
lemma2 A (natrec x₁ a a₁ a₂) | n , ne x , proj₃ =
  _ , ne (natrec x) , natrec-subst* x₁ a a₁ proj₃
lemma2 A (conv a₁ x) = let a , b , c = lemma2 (syntacticTerm a₁) a₁
                       in  a , b , conv* c x

lemma1 : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
lemma1 (ℕ x) = ℕ , ℕ , id (ℕ x)
lemma1 (U x) = U , U , id (U x)
lemma1 (Π A ▹ A₁) = Π _ ▹ _ , Π , id (Π A ▹ A₁)
lemma1 (univ x) = let a , b , c = lemma2 (U (wfTerm x)) x
                  in  a , b , univ* c

lemy : ∀ {n R T Γ} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
lemy here here = PE.refl
lemy (there n∷R) (there n∷T) rewrite lemy n∷R n∷T = PE.refl

lem4 : ∀ {x A B Γ} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
lem4 A B x∷A x∷B rewrite lemy x∷A x∷B = refl A

lemma3 : ∀ {t A B Γ} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
lemma3 (var x) (var x₁ x₂) (var x₃ x₄) =
  lem4 (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
lemma3 (_∘_ neT) (t∷A ∘ t∷A₁) (t∷B ∘ t∷B₁) with lemma3 neT t∷A t∷B
... | q = let w = proj₂ (injectivity q)
          in  substTypeEq w (refl t∷A₁)
lemma3 (natrec neT) (natrec x t∷A t∷A₁ t∷A₂) (natrec x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
lemma3 x (conv t∷A x₁) t∷B = let q = lemma3 x t∷A t∷B
                             in  trans (sym x₁) q
lemma3 x t∷A (conv t∷B x₃) = let q = lemma3 x t∷A t∷B
                             in  trans q x₃

lemma4 : ∀ {v k R T Γ}
       → Neutral k → Γ ⊢ v ∷ R → Γ ⊢ v ∷ T → Γ ⊢ v ⇒ k ∷ R
       → Γ ⊢ T ≡ R
lemma4 neK v∷R v∷T (conv d x) =
  let q = lemma4 neK (conv v∷R (sym x)) v∷T d
  in  trans q x
lemma4 (_∘_ neU) v∷R v∷T (app-subst d x) =
  let F , G , t , a , A≡G[a] = inversion-app v∷T
      q = lemma4 neU (redFirstTerm d) t d
      w , r = injectivity q
  in  trans A≡G[a] (substTypeEq r (refl a))
lemma4 neK v∷R v∷T (β-red x x₁ x₂) =
  let F , G , t , a , A≡G[a] = inversion-app v∷T
      q = lemma3 {!{- Neutral (t [ a ]) → Neutral t -}!}
                 {!{- Γ ⊢ lam t ∷ Π F ▹ G → Γ ∙ F ⊢ t ∷ G -}!} x₁
  in  trans A≡G[a] (substTypeEq q (refl x₂))
lemma4 neK v∷R v∷T (natrec-subst x x₁ x₂ d) =
  let _ , _ , _ , _ , d = inversion-natrec v∷T
  in  d
lemma4 neK v∷R v∷T (natrec-zero x x₁ x₂) =
  let _ , _ , _ , _ , d = inversion-natrec v∷T
  in  d
lemma4 neK v∷R v∷T (natrec-suc x x₁ x₂ x₃) =
  let _ , _ , _ , _ , d = inversion-natrec v∷T
  in  d
