module Definition.Conversion.Lift where

open import Definition.Untyped as U
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Injectivity
import Definition.LogicalRelation.Consequences.Inequality as WF
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.Substitution
open import Definition.LogicalRelation.Consequences.SingleSubst
open import Definition.LogicalRelation.Consequences.Reduction

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


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


mutual
  lift~toConv↓' : ∀ {t u A A' Γ l}
                → Γ ⊩⟨ l ⟩ A'
                → Γ ⊢ A' ⇒* A
                → Γ ⊢ t ~ u ↓ A
                → Γ ⊢ t [conv↓] u ∷ A
  lift~toConv↓' (U' .⁰ 0<1 ⊢Γ) D ([~] A D₁ whnfB k~l)
                rewrite PE.sym (whnfRed*' D U) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (conv (soundness~↑ k~l) (subset* D₁))
    in  univ ⊢t ⊢u (ne ([~] A D₁ U k~l))
  lift~toConv↓' (ℕ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet*' (red D , ℕ) (D₁ , whnfB)) =
    ℕ-ins ([~] A D₂ ℕ k~l)
  lift~toConv↓' (ne' K D neK K≡K) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet*' (red D , ne neK) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑ k~l)
        A≡K = subset* D₂
    in  ne-ins (conv ⊢t A≡K) (conv ⊢u A≡K) neK ([~] A D₂ (ne neK) k~l)
  lift~toConv↓' (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet*' (red D , Π) (D₁ , whnfB)) =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ ([~] A D₂ Π k~l))
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        neT , neU = ne~↑ k~l
        ⊢Γ = wf ⊢F
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
                       (refl (var (⊢Γ ∙ ⊢F) here))
        0≡0 = lift~toConv↑' ([F] (step id) (⊢Γ ∙ ⊢F)) (var (var (⊢Γ ∙ ⊢F) here))
        k∘0≡l∘0 = lift~toConv↑' ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (app (wk~↓ (step id) (⊢Γ ∙ ⊢F) ([~] A D₂ Π k~l))
                                     0≡0)
    in  fun-ext ⊢F ⊢t ⊢u (ne neT) (ne neU)
                (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                          (substVar0Id _)
                          k∘0≡l∘0)
  lift~toConv↓' (emb 0<1 [A]) D t~u = lift~toConv↓' [A] D t~u

  lift~toConv↑' : ∀ {t u A Γ l}
                → Γ ⊩⟨ l ⟩ A
                → Γ ⊢ t ~ u ↑ A
                → Γ ⊢ t [conv↑] u ∷ A
  lift~toConv↑' [A] t~u =
    let B , whnfB , D = fullyReducible' [A]
        t~u↓ = [~] _ (red D) whnfB t~u
        neT , neU = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  [↑]ₜ _ _ _ (red D) (id ⊢t) (id ⊢u) whnfB
             (ne neT) (ne neU) (lift~toConv↓' [A] (red D) t~u↓)

lift~toConv↓ : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↓ A
             → Γ ⊢ t [conv↓] u ∷ A
lift~toConv↓ ([~] A₁ D whnfB k~l) with fundamental (proj₁ (syntacticRed D))
lift~toConv↓ ([~] A₁ D whnfB k~l) | [Γ] , [A₁] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA₁] = irrelevance' (idSubst-lemma₀ A₁) (proj₁ ([A₁] ⊢Γ idSubst))
  in  lift~toConv↓' [idA₁] D ([~] A₁ D whnfB k~l)

lift~toConv↑ : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↑ A
             → Γ ⊢ t [conv↑] u ∷ A
lift~toConv↑ t~u with fundamental (proj₁ (syntacticEqTerm (soundness~↑ t~u)))
lift~toConv↑ t~u | [Γ] , [A] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA] = irrelevance' (idSubst-lemma₀ _) (proj₁ ([A] ⊢Γ idSubst))
  in  lift~toConv↑' [idA] t~u
