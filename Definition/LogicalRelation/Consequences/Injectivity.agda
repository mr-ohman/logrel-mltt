module Definition.LogicalRelation.Consequences.Injectivity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps

open import Definition.LogicalRelation
import Definition.LogicalRelation.Weakening as LR
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Soundness
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Fundamental

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product

import Relation.Binary.PropositionalEquality as PE


substVar0Id' : ∀ x → (purge (lift (step id)) (consSubst idSubst (var zero)))
       x
       PE.≡ idSubst x
substVar0Id' zero = PE.refl
substVar0Id' (suc x) = PE.refl

substVar0Id : ∀ F → (U.wk (lift (step id)) F) [ var zero ] PE.≡ F
substVar0Id F = PE.trans (subst-wk F) (PE.trans (substEq substVar0Id' F) (substIdEq F))

Π-inj'' : ∀ {F G Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
             → Γ ⊢ F
             × Γ ∙ F ⊢ G
Π-inj'' (noemb (Π F G D ⊢F ⊢G [F] [G] G-ext)) =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
  in  PE.subst (λ x → _ ⊢ x) (PE.sym F≡F₁) ⊢F
  ,   PE.subst₂ (λ x y → _ ∙ x ⊢ y) (PE.sym F≡F₁) (PE.sym G≡G₁) ⊢G
Π-inj'' (emb 0<1 x) = Π-inj'' x

Π-inj' : ∀ {F G Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
             → Γ ⊢ F
             × Γ ∙ F ⊢ G
Π-inj' [ΠFG] = Π-inj'' (Π-elim [ΠFG])

Π-inj : ∀ {Γ F G} → Γ ⊢ Π F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
Π-inj ⊢ΠFG with fundamental ⊢ΠFG
Π-inj {Γ} {F} {G} ⊢ΠFG | [Γ] , [ΠFG] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      eq₁ = PE.cong₂ Π_▹_ (substIdEq F) (PE.trans (substEq liftIdSubst G) (substIdEq G))
      [ΠFG]₁ = proj₁ ([ΠFG] ⊢Γ [id])
      [ΠFG]' = PE.subst (λ x → Γ ⊩⟨ ¹ ⟩ x) eq₁ [ΠFG]₁
  in  Π-inj' [ΠFG]'

Π≡-inj'' : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / Π-intr [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
Π≡-inj'' (noemb (Π F G D ⊢F ⊢G [F] [G] G-ext))
         Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
      H≡F' , E≡G' = Π-PE-injectivity (whnfRed*' D' Π)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]' = irrelevance' (PE.trans (wk-id _ zero) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]' = PE.subst₂ (λ x y → _ ∙ y ⊩⟨ _ ⟩ x)
                       (PE.trans (substVar0Id _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F'] id ⊢Γ
      [F≡H]' = irrelevanceEq'' (PE.trans (wk-id _ zero) (PE.sym F≡F₁))
                               (PE.trans (wk-id _ zero) (PE.sym H≡F'))
                               [F]₁ [F]' [F≡H]₁
      [G≡E]₁ = [G≡G'] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]' = irrelevanceEqLift'' (PE.trans (substVar0Id _) (PE.sym G≡G₁))
                                   (PE.trans (substVar0Id _) (PE.sym E≡G'))
                                   (PE.sym F≡F₁) [G]₁ [G]' [G≡E]₁
  in  soundnessEq [F]' [F≡H]' , soundnessEq [G]' [G≡E]'
Π≡-inj'' (emb 0<1 x) [ΠFG≡ΠHE] = Π≡-inj'' x [ΠFG≡ΠHE]

Π≡-inj' : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
Π≡-inj' [ΠFG] [ΠFG≡ΠHE] =
  Π≡-inj'' (Π-elim [ΠFG]) (irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠHE])

Π≡-inj : ∀ {Γ F G H E} → Γ ⊢ Π F ▹ G ≡ Π H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
Π≡-inj ⊢ΠFG≡ΠHE with fundamentalEq ⊢ΠFG≡ΠHE
Π≡-inj {Γ} {F} {G} {H} {E} ⊢ΠFG≡ΠHE | [Γ] , [ΠFG] , [ΠHE] , [ΠFG≡ΠHE] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      eq₁ = PE.cong₂ Π_▹_ (substIdEq F) (PE.trans (substEq liftIdSubst G) (substIdEq G))
      eq₂ = PE.cong₂ Π_▹_ (substIdEq H) (PE.trans (substEq liftIdSubst E) (substIdEq E))
      [ΠFG]₁ = proj₁ ([ΠFG] ⊢Γ [id])
      [ΠFG]' = PE.subst (λ x → Γ ⊩⟨ ¹ ⟩ x) eq₁ [ΠFG]₁
      [ΠFG≡ΠHE]' = irrelevanceEq'' eq₁ eq₂ [ΠFG]₁ [ΠFG]' ([ΠFG≡ΠHE] ⊢Γ [id])
  in  Π≡-inj' [ΠFG]' [ΠFG≡ΠHE]'

-- TODO rename to eq-inj and similar
eq-inj : ∀ {A B Γ} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
eq-inj A≡B with fundamentalEq A≡B
eq-inj A≡B | [Γ] , [A] , [B] , [A≡B] = soundnessₛ [Γ] [A] , soundnessₛ [Γ] [B]

term-inj : ∀ {t A Γ} → Γ ⊢ t ∷ A → Γ ⊢ A
term-inj t with fundamentalTerm t
term-inj t | [Γ] , [A] , [t] = soundnessₛ [Γ] [A]

eqTerm-inj : ∀ {t u A Γ} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
eqTerm-inj t≡u with fundamentalTermEq t≡u
eqTerm-inj t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  soundnessₛ [Γ] [A] , soundnessTermₛ [Γ] [A] [t] , soundnessTermₛ [Γ] [A] [u]
