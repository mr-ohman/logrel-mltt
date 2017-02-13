module Definition.LogicalRelation.Consequences.SingleSubst where

open import Definition.Untyped

open import Definition.Typed
open import Definition.Typed.EqRelInstance

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Wellformed
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Fundamental
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Product


substType : ∀ {t F G Γ} → Γ ∙ F ⊢ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substType ⊢G ⊢t with fundamental ⊢G | fundamentalTerm ⊢t
substType {t} {F} {G} ⊢G ⊢t | [Γ] , [G] | [Γ]' , [F] , [t] =
  let [G]' = S.irrelevance {A = G} [Γ] ([Γ]' ∙ [F]) [G]
      [G[t]] = substS {F} {G} {t} [Γ]' [F] [G]' [t]
  in  wellformedₛ [Γ]' [G[t]]

substTypeEq : ∀ {t u F G E Γ} → Γ ∙ F ⊢ G ≡ E → Γ ⊢ t ≡ u ∷ F → Γ ⊢ G [ t ] ≡ E [ u ]
substTypeEq ⊢G ⊢t with fundamentalEq ⊢G | fundamentalTermEq ⊢t
substTypeEq {t} {u} {F} {G} {E} ⊢G ⊢t | [Γ] , [G] , [E] , [G≡E] |
  [Γ]' , modelsTermEq [F] [t] [u] [t≡u] =
  let [G]' = S.irrelevance {A = G} [Γ] ([Γ]' ∙ [F]) [G]
      [E]' = S.irrelevance {A = E} [Γ] ([Γ]' ∙ [F]) [E]
      [G≡E]' = S.irrelevanceEq {A = G} {B = E} [Γ] ([Γ]' ∙ [F]) [G] [G]' [G≡E]
      [G[t]] = substS {F} {G} {t} [Γ]' [F] [G]' [t]
      [G≡E[t]] = substSEq {F} {F} {G} {E} {t} {u} [Γ]'
                          [F] [F] (reflₛ {F} [Γ]' [F])
                          [G]' [E]' [G≡E]'
                          [t] [u] [t≡u]
  in  wellformedEqₛ [Γ]' [G[t]] [G≡E[t]]

substTerm : ∀ {F G t f Γ} → Γ ∙ F ⊢ f ∷ G → Γ ⊢ t ∷ F → Γ ⊢ f [ t ] ∷ G [ t ]
substTerm {F} {G} {t} {f} ⊢f ⊢t with fundamentalTerm ⊢f | fundamentalTerm ⊢t
substTerm {F} {G} {t} {f} ⊢f ⊢t | [Γ] , [G] , [f] | [Γ]' , [F] , [t] =
  let [G]' = S.irrelevance {A = G} [Γ] ([Γ]' ∙ [F]) [G]
      [G[t]] = substS {F} {G} {t} [Γ]' [F] [G]' [t]
      [f]' = S.irrelevanceTerm {A = G} {t = f} [Γ] ([Γ]' ∙ [F]) [G] [G]' [f]
      [t[u]] = substSTerm {F} {G} {t} {f} [Γ]' [F] [G]' [f]' [t]
  in  wellformedTermₛ [Γ]' [G[t]] [t[u]]

substTypeΠ : ∀ {t F G Γ} → Γ ⊢ Π F ▹ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

subst↑Type : ∀ {t F G Γ}
           → Γ ∙ F ⊢ G
           → Γ ∙ F ⊢ t ∷ wk1 F
           → Γ ∙ F ⊢ G [ t ]↑
subst↑Type ⊢G ⊢t with fundamental ⊢G | fundamentalTerm ⊢t
subst↑Type {t} {F} {G} ⊢G ⊢t | [Γ] ∙ [F] , [G] | [Γ]' , [wk1F] , [t] =
  let [F]' = maybeEmbₛ {A = F} [Γ] [F]
      [Γ∙F] = _∙_ {A = F} [Γ] [F]
      [Γ∙F]' = [Γ] ∙ [F]'
      [G]' = S.irrelevance {A = G} [Γ∙F] [Γ∙F]' [G]
      [wk1F]' = wk1ₛ {F} {F} [Γ] [F]' [F]'
      [t]' = S.irrelevanceTerm {A = wk1 F} {t = t} [Γ]' [Γ∙F]' [wk1F] [wk1F]' [t]
      [G[t]] = subst↑S {F} {G} {t} [Γ] [F]' [G]' [t]'
  in  wellformedₛ [Γ∙F]' [G[t]]

subst↑TypeEq : ∀ {t u F G E Γ}
             → Γ ∙ F ⊢ G ≡ E
             → Γ ∙ F ⊢ t ≡ u ∷ wk1 F
             → Γ ∙ F ⊢ G [ t ]↑ ≡ E [ u ]↑
subst↑TypeEq ⊢G ⊢t with fundamentalEq ⊢G | fundamentalTermEq ⊢t
subst↑TypeEq {t} {u} {F} {G} {E} ⊢G ⊢t | [Γ] ∙ [F] , [G] , [E] , [G≡E] |
  [Γ]' , modelsTermEq [wk1F] [t] [u] [t≡u] =
  let [F]' = maybeEmbₛ {A = F} [Γ] [F]
      [Γ∙F] = _∙_ {A = F} [Γ] [F]
      [Γ∙F]' = [Γ] ∙ [F]'
      [G]' = S.irrelevance {A = G} [Γ∙F] [Γ∙F]' [G]
      [E]' = S.irrelevance {A = E} [Γ∙F] [Γ∙F]' [E]
      [G≡E]' = S.irrelevanceEq {A = G} {B = E} [Γ∙F] [Γ∙F]' [G] [G]' [G≡E]
      [wk1F]' = wk1ₛ {F} {F} [Γ] [F]' [F]'
      [t]' = S.irrelevanceTerm {A = wk1 F} {t = t} [Γ]' [Γ∙F]' [wk1F] [wk1F]' [t]
      [u]' = S.irrelevanceTerm {A = wk1 F} {t = u} [Γ]' [Γ∙F]' [wk1F] [wk1F]' [u]
      [t≡u]' = S.irrelevanceEqTerm {A = wk1 F} {t = t} {u = u}
                                   [Γ]' [Γ∙F]' [wk1F] [wk1F]' [t≡u]
      [G[t]] = subst↑S {F} {G} {t} [Γ] [F]' [G]' [t]'
      [G≡E[t]] = subst↑SEq {F} {G} {E} {t} {u} [Γ]
                           [F]' [G]' [E]' [G≡E]'
                           [t]' [u]' [t≡u]'
  in  wellformedEqₛ ([Γ] ∙ [F]') [G[t]] [G≡E[t]]
