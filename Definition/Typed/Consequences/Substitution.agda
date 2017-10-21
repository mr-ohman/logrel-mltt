{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Substitution where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Typed.Weakening as T
open import Definition.Typed.Consequences.Syntactic
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE


-- Well-formed substitution of types.
substitution : ∀ {A Γ Δ σ} → Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A
substitution A σ ⊢Δ with fundamental A | fundamentalSubst (wf A) ⊢Δ σ
substitution A σ ⊢Δ | [Γ] , [A] | [Γ]′ , [σ] =
  escape (proj₁ ([A] ⊢Δ (S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ])))

-- Well-formed substitution of type equality.
substitutionEq : ∀ {A B Γ Δ σ σ′}
               → Γ ⊢ A ≡ B → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ≡ subst σ′ B
substitutionEq A≡B σ ⊢Δ with fundamentalEq A≡B | fundamentalSubstEq (wfEq A≡B) ⊢Δ σ
substitutionEq A≡B σ ⊢Δ | [Γ] , [A] , [B] , [A≡B] | [Γ]′ , [σ] , [σ′] , [σ≡σ′]  =
  let [σ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeEq (proj₁ ([A] ⊢Δ [σ]′))
                   (transEq (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([B] ⊢Δ [σ]′))
                            (proj₁ ([B] ⊢Δ [σ′]′)) ([A≡B] ⊢Δ [σ]′)
                            (proj₂ ([B] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Well-formed substitution of terms.
substitutionTerm : ∀ {t A Γ Δ σ}
               → Γ ⊢ t ∷ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ t ∷ subst σ A
substitutionTerm t σ ⊢Δ with fundamentalTerm t | fundamentalSubst (wfTerm t) ⊢Δ σ
substitutionTerm t σ ⊢Δ | [Γ] , [A] , [t] | [Γ]′ , [σ] =
  let [σ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  escapeTerm (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([t] ⊢Δ [σ]′))

-- Well-formed substitution of term equality.
substitutionEqTerm : ∀ {t u A Γ Δ σ σ′}
                   → Γ ⊢ t ≡ u ∷ A → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ
                   → Δ ⊢ subst σ t ≡ subst σ′ u ∷ subst σ A
substitutionEqTerm t≡u σ≡σ′ ⊢Δ with fundamentalTermEq t≡u
                                  | fundamentalSubstEq (wfEqTerm t≡u) ⊢Δ σ≡σ′
... | [Γ] , modelsTermEq [A] [t] [u] [t≡u] | [Γ]′ , [σ] , [σ′] , [σ≡σ′] =
  let [σ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeTermEq (proj₁ ([A] ⊢Δ [σ]′))
                       (transEqTerm (proj₁ ([A] ⊢Δ [σ]′)) ([t≡u] ⊢Δ [σ]′)
                                    (proj₂ ([u] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Reflexivity of well-formed substitution.
substRefl : ∀ {σ Γ Δ}
          → Δ ⊢ˢ σ ∷ Γ
          → Δ ⊢ˢ σ ≡ σ ∷ Γ
substRefl id = id
substRefl (σ , x) = substRefl σ , refl x

-- Weakening of well-formed substitution.
wkSubst′ : ∀ {ρ σ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊢ˢ σ ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ∷ Γ
wkSubst′ ε ⊢Δ ⊢Δ′ ρ id = id
wkSubst′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) =
  wkSubst′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ
  , PE.subst (λ x → _ ⊢ _ ∷ x) (wk-subst A) (wkTerm ρ ⊢Δ′ headσ)

-- Weakening of well-formed substitution by one.
wk1Subst′ : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ]

-- Lifting of well-formed substitution.
liftSubst′ : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F)
             ([σ] : Δ ⊢ˢ σ ∷ Γ)
           → (Δ ∙ subst σ F) ⊢ˢ liftSubst σ ∷ Γ ∙ F
liftSubst′ {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
  in  wkSubst′ ⊢Γ ⊢Δ ⊢Δ∙F (T.step T.id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                         (wk-subst F) here)

-- Well-formed identity substitution.
idSubst′ : ∀ {Γ} (⊢Γ : ⊢ Γ)
         → Γ ⊢ˢ idSubst ∷ Γ
idSubst′ ε = id
idSubst′ (_∙_ {Γ} {A} ⊢Γ ⊢A) =
  wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
  , PE.subst (λ x → Γ ∙ A ⊢ _ ∷ x) (wk1-tailId A) (var (⊢Γ ∙ ⊢A) here)

-- Well-formed substitution composition.
substComp′ : ∀ {σ σ′ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([σ] : Δ′ ⊢ˢ σ ∷ Δ)
             ([σ′] : Δ ⊢ˢ σ′ ∷ Γ)
           → Δ′ ⊢ˢ σ ₛ•ₛ σ′ ∷ Γ
substComp′ ε ⊢Δ ⊢Δ′ [σ] id = id
substComp′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ [σ] ([tailσ′] , [headσ′]) =
  substComp′ ⊢Γ ⊢Δ ⊢Δ′ [σ] [tailσ′]
  , PE.subst (λ x → _ ⊢ _ ∷ x) (substCompEq A)
             (substitutionTerm [headσ′] [σ] ⊢Δ′)

-- Well-formed singleton substitution of terms.
singleSubst : ∀ {A t Γ} → Γ ⊢ t ∷ A → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A
singleSubst {A} t =
  let ⊢Γ = wfTerm t
  in  idSubst′ ⊢Γ , PE.subst (λ x → _ ⊢ _ ∷ x) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of term equality.
singleSubstEq : ∀ {A t u Γ} → Γ ⊢ t ≡ u ∷ A
              → Γ ⊢ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
singleSubstEq {A} t =
  let ⊢Γ = wfEqTerm t
  in  substRefl (idSubst′ ⊢Γ) , PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of terms with lifting.
singleSubst↑ : ∀ {A t Γ} → Γ ∙ A ⊢ t ∷ wk1 A → Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ A
singleSubst↑ {A} t with wfTerm t
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
              , PE.subst (λ x → _ ∙ A ⊢ _ ∷ x) (wk1-tailId A) t

-- Well-formed singleton substitution of term equality with lifting.
singleSubst↑Eq : ∀ {A t u Γ} → Γ ∙ A ⊢ t ≡ u ∷ wk1 A
              → Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ≡ consSubst (wk1Subst idSubst) u ∷ Γ ∙ A
singleSubst↑Eq {A} t with wfEqTerm t
... | ⊢Γ ∙ ⊢A = substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ))
              , PE.subst (λ x → _ ∙ A ⊢ _ ≡ _ ∷ x) (wk1-tailId A) t

-- Helper lemmas for single substitution

substType : ∀ {t F G Γ} → Γ ∙ F ⊢ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substType {t} {F} {G} ⊢G ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitution ⊢G (singleSubst ⊢t) ⊢Γ

substTypeEq : ∀ {t u F G E Γ} → Γ ∙ F ⊢ G ≡ E → Γ ⊢ t ≡ u ∷ F → Γ ⊢ G [ t ] ≡ E [ u ]
substTypeEq {F = F} ⊢G ⊢t =
  let ⊢Γ = wfEqTerm ⊢t
  in  substitutionEq ⊢G (singleSubstEq ⊢t) ⊢Γ

substTerm : ∀ {F G t f Γ} → Γ ∙ F ⊢ f ∷ G → Γ ⊢ t ∷ F → Γ ⊢ f [ t ] ∷ G [ t ]
substTerm {F} {G} {t} {f} ⊢f ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitutionTerm ⊢f (singleSubst ⊢t) ⊢Γ

substTypeΠ : ∀ {t F G Γ} → Γ ⊢ Π F ▹ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

subst↑Type : ∀ {t F G Γ}
           → Γ ∙ F ⊢ G
           → Γ ∙ F ⊢ t ∷ wk1 F
           → Γ ∙ F ⊢ G [ t ]↑
subst↑Type ⊢G ⊢t = substitution ⊢G (singleSubst↑ ⊢t) (wfTerm ⊢t)

subst↑TypeEq : ∀ {t u F G E Γ}
             → Γ ∙ F ⊢ G ≡ E
             → Γ ∙ F ⊢ t ≡ u ∷ wk1 F
             → Γ ∙ F ⊢ G [ t ]↑ ≡ E [ u ]↑
subst↑TypeEq ⊢G ⊢t = substitutionEq ⊢G (singleSubst↑Eq ⊢t) (wfEqTerm ⊢t)
