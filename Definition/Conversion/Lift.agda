{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Lift where

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Reduction

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Lifting of algorithmic equality of types from WHNF to generic types.
liftConv : ∀ {A B}
          → Γ ⊢ A [conv↓] B
          → Γ ⊢ A [conv↑] B
liftConv A<>B =
  let ⊢A , ⊢B = syntacticEq (soundnessConv↓ A<>B)
      whnfA , whnfB = whnfConv↓ A<>B
  in  [↑] _ _ (id ⊢A) (id ⊢B) whnfA whnfB A<>B

-- Lifting of algorithmic equality of terms from WHNF to generic terms.
liftConvTerm : ∀ {t u A}
             → Γ ⊢ t [conv↓] u ∷ A
             → Γ ⊢ t [conv↑] u ∷ A
liftConvTerm t<>u =
  let ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundnessConv↓Term t<>u)
      whnfA , whnfT , whnfU = whnfConv↓Term t<>u
  in  [↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢u) whnfA whnfT whnfU t<>u


mutual
  -- Helper function for lifting from neutrals to generic terms in WHNF.
  lift~toConv↓′ : ∀ {t u A A′ l}
                → Γ ⊩⟨ l ⟩ A′
                → Γ ⊢ A′ ⇒* A
                → Γ ⊢ t ~ u ↓ A
                → Γ ⊢ t [conv↓] u ∷ A
  lift~toConv↓′ (Uᵣ′ .⁰ 0<1 ⊢Γ) D ([~] A D₁ whnfB k~l)
                rewrite PE.sym (whnfRed* D Uₙ) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (conv (soundness~↑ k~l) (subset* D₁))
    in  univ ⊢t ⊢u (ne ([~] A D₁ Uₙ k~l))
  lift~toConv↓′ (ℕᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ℕₙ) (D₁ , whnfB)) =
    ℕ-ins ([~] A D₂ ℕₙ k~l)
  lift~toConv↓′ (Emptyᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , Emptyₙ) (D₁ , whnfB)) =
    Empty-ins ([~] A D₂ Emptyₙ k~l)
  lift~toConv↓′ (Unitᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , Unitₙ) (D₁ , whnfB)) =
    Unit-ins ([~] A D₂ Unitₙ k~l)
  lift~toConv↓′ (ne′ K D neK K≡K) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ne neK) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑ k~l)
        A≡K = subset* D₂
    in  ne-ins (conv ⊢t A≡K) (conv ⊢u A≡K) neK ([~] A D₂ (ne neK) k~l)
  lift~toConv↓′ (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , Πₙ) (D₁ , whnfB)) =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ ([~] A D₂ Πₙ k~l))
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        neT , neU = ne~↑ k~l
        ⊢Γ = wf ⊢F
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var x0) (var (⊢Γ ∙ ⊢F) here)
                       (refl (var (⊢Γ ∙ ⊢F) here))
        0≡0 = lift~toConv↑′ ([F] (step id) (⊢Γ ∙ ⊢F)) (var-refl (var (⊢Γ ∙ ⊢F) here) PE.refl)
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (app-cong (wk~↓ (step id) (⊢Γ ∙ ⊢F) ([~] A D₂ Πₙ k~l))
                                          0≡0)
    in  η-eq ⊢t ⊢u (ne neT) (ne neU)
             (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x)
                       (wkSingleSubstId _)
                       k∘0≡l∘0)
  lift~toConv↓′ (Σᵣ′ F G D ⊢F ⊢G Σ≡Σ [F] [G] G-ext) D₁ ([~] A″ D₂ whnfA t~u)
                rewrite PE.sym (whrDet* (red D , Σₙ) (D₁ , whnfA)) {- Σ F ▹ G ≡ A -} =
    let neT , neU = ne~↑ t~u
        t~u↓ = [~] A″ D₂ Σₙ t~u
        ⊢ΣFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        ⊢Γ = wf ⊢F

        wkId = wk-id F
        wkLiftId = PE.cong (λ x → x [ fst _ ]) (wk-lift-id G)

        wk[F] = [F] id ⊢Γ
        wk⊢fst = PE.subst (λ x → _ ⊢ _ ∷ x) (PE.sym wkId) (fstⱼ ⊢F ⊢G ⊢t)
        wkfst≡ = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (PE.sym wkId) (fst-cong ⊢F ⊢G (refl ⊢t))
        wk[fst] = neuTerm wk[F] (fstₙ neT) wk⊢fst wkfst≡
        wk[Gfst] = [G] id ⊢Γ wk[fst]

        wkfst~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkId) (fst-cong t~u↓)
        wksnd~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkLiftId) (snd-cong t~u↓)
    in  Σ-η ⊢t ⊢u (ne neT) (ne neU)
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkId
                      (lift~toConv↑′ wk[F] wkfst~))
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkLiftId
                      (lift~toConv↑′ wk[Gfst] wksnd~))
  lift~toConv↓′ (emb 0<1 [A]) D t~u = lift~toConv↓′ [A] D t~u

  -- Helper function for lifting from neutrals to generic terms.
  lift~toConv↑′ : ∀ {t u A l}
                → Γ ⊩⟨ l ⟩ A
                → Γ ⊢ t ~ u ↑ A
                → Γ ⊢ t [conv↑] u ∷ A
  lift~toConv↑′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (red D) whnfB t~u
        neT , neU = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  [↑]ₜ _ _ _ (red D) (id ⊢t) (id ⊢u) whnfB
             (ne neT) (ne neU) (lift~toConv↓′ [A] (red D) t~u↓)

-- Lifting of algorithmic equality of terms from neutrals to generic terms in WHNF.
lift~toConv↓ : ∀ {t u A}
             → Γ ⊢ t ~ u ↓ A
             → Γ ⊢ t [conv↓] u ∷ A
lift~toConv↓ ([~] A₁ D whnfB k~l) =
  lift~toConv↓′ (reducible (proj₁ (syntacticRed D))) D ([~] A₁ D whnfB k~l)

-- Lifting of algorithmic equality of terms from neutrals to generic terms.
lift~toConv↑ : ∀ {t u A}
             → Γ ⊢ t ~ u ↑ A
             → Γ ⊢ t [conv↑] u ∷ A
lift~toConv↑ t~u =
  lift~toConv↑′ (reducible (proj₁ (syntacticEqTerm (soundness~↑ t~u)))) t~u
