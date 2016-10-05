module Lemma.Consequences where

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product


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
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Lemma.Fundamental

import Relation.Binary.PropositionalEquality as PE


sucᵏ : Nat → Term
sucᵏ zero = zero
sucᵏ (suc n) = suc (sucᵏ n)

noNe : ∀ {t A} → ε ⊢ t ∷ A → Neutral t → ⊥
noNe (var x₁ ()) (var x)
noNe (conv ⊢t x) (var n) = noNe ⊢t (var n)
noNe (⊢t ∘ ⊢t₁) (_∘_ neT) = noNe ⊢t neT
noNe (conv ⊢t x) (_∘_ neT) = noNe ⊢t (_∘_ neT)
noNe (natrec x ⊢t ⊢t₁ ⊢t₂) (natrec neT) = noNe ⊢t₂ neT
noNe (conv ⊢t x) (natrec neT) = noNe ⊢t (natrec neT)

canonicity' : ∀ {t l} → ([ℕ] : ε ⊩⟨ l ⟩ ℕ) → ε ⊩⟨ l ⟩ t ∷ ℕ / [ℕ] → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity' {l = l} (ℕ D) ℕ[ _ , d , suc , prop ] =
  let a , b = canonicity' {l = l} (ℕ D) prop
  in  suc a , trans (subset*Term (redₜ d)) (suc-cong b)
canonicity' (ℕ D) ℕ[ .zero , d , zero , prop ] = zero , subset*Term (redₜ d)
canonicity' (ℕ D) ℕ[ n , d , ne x , prop ] = ⊥-elim (noNe prop x)
canonicity' (ne D neK) [t] = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
canonicity' (Π D ⊢F ⊢G [F] [G] G-ext) [t] = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
canonicity' (emb {l< = 0<1} x) [t] = canonicity' x [t]

canonicity : ∀ {t} → ε ⊢ t ∷ ℕ → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity ⊢t with fundamentalTerm ⊢t
canonicity ⊢t | ε , [ℕ] , [t] =
  let [ℕ]' = proj₁ ([ℕ] {σ = idSubst} ε tt)
      [t]' = irrelevanceTerm'' PE.refl (substIdEq _) [ℕ]' [ℕ]' (proj₁ ([t] ε tt))
  in  canonicity' [ℕ]' [t]'

substVar0Id' : ∀ x → (purge (lift (step id)) (consSubst idSubst (var zero)))
       x
       PE.≡ idSubst x
substVar0Id' zero = PE.refl
substVar0Id' (suc x) = PE.refl

substVar0Id : ∀ F → (U.wk (lift (step id)) F) [ var zero ] PE.≡ F
substVar0Id F = PE.trans (subst-wk F) (PE.trans (substEq substVar0Id' F) (substIdEq F))

injectivity' : ∀ {F G H E Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
             → Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π H ▹ E / [ΠFG]
             → Γ ⊢ F ≡ H
             × Γ ∙ F ⊢ G ≡ E
injectivity' (ℕ D) [ΠFG≡ΠHE] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
injectivity' (ne D neK) [ΠFG≡ΠHE] = ⊥-elim ((Π≢ne neK (whnfRed*' (red D) Π)))
injectivity' (Π D ⊢F ⊢G [F] [G] G-ext) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  let F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed*' (red D) Π)
      H≡F' , E≡G' = Π-PE-injectivity (whnfRed*' D' Π)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.trans (wk-id _ zero) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var zero) (var (⊢Γ ∙ ⊢F) here)
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]' = PE.subst₂ (λ x y → _ ∙ y ⊩⟨ _ ⟩ x) (PE.trans (substVar0Id _) (PE.sym G≡G₁)) (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F'] id ⊢Γ
      [F≡H]' = irrelevanceEq'' (PE.trans (wk-id _ zero) (PE.sym F≡F₁)) (PE.trans (wk-id _ zero) (PE.sym H≡F')) [F]₁ [F]' [F≡H]₁
      [G≡E]₁ = [G≡G'] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]' = irrelevanceEqLift'' (PE.trans (substVar0Id _) (PE.sym G≡G₁)) (PE.trans (substVar0Id _) (PE.sym E≡G')) (PE.sym F≡F₁) [G]₁ [G]' [G≡E]₁
  in  soundnessEq [F]' [F≡H]' , soundnessEq [G]' [G≡E]'
injectivity' (emb {l< = 0<1} x) [ΠFG≡ΠHE] = injectivity' x [ΠFG≡ΠHE]

injectivity : ∀ {Γ F G H E} → Γ ⊢ Π F ▹ G ≡ Π H ▹ E → Γ ⊢ F ≡ H × Γ ∙ F ⊢ G ≡ E
injectivity ⊢ΠFG≡ΠHE with fundamentalEq ⊢ΠFG≡ΠHE
injectivity {Γ} {F} {G} {H} {E} ⊢ΠFG≡ΠHE | [Γ] , [ΠFG] , [ΠHE] , [ΠFG≡ΠHE] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      eq₁ = PE.cong₂ Π_▹_ (substIdEq F) (PE.trans (substEq liftIdSubst G) (substIdEq G))
      eq₂ = PE.cong₂ Π_▹_ (substIdEq H) (PE.trans (substEq liftIdSubst E) (substIdEq E))
      [ΠFG]₁ = proj₁ ([ΠFG] ⊢Γ [id])
      [ΠFG]' = PE.subst (λ x → Γ ⊩⟨ ¹ ⟩ x) eq₁ [ΠFG]₁
      [ΠFG≡ΠHE]' = irrelevanceEq'' eq₁ eq₂ [ΠFG]₁ [ΠFG]' ([ΠFG≡ΠHE] ⊢Γ [id])
  in  injectivity' [ΠFG]' [ΠFG≡ΠHE]'
