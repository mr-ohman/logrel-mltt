open import Definition.EqualityRelation

module Definition.LogicalRelation.Substitution.Properties {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening as LR

open import Tools.Nat
open import Tools.Unit
open import Tools.Product
import Tools.PropositionalEquality as PE


consSubstS : ∀ {l σ t A Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
           ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
           ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
           ([t] : Δ ⊩⟨ l ⟩ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ]))
         → Δ ⊩ₛ consSubst σ t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
consSubstS [Γ] ⊢Δ [σ] [A] [t] = [σ] , [t]

consSubstSEq : ∀ {l σ σ' t A Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
             ([σ]    : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ'] : Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
             ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
             ([t] : Δ ⊩⟨ l ⟩ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ]))
           → Δ ⊩ₛ consSubst σ t ≡ consSubst σ' t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
               / consSubstS {t = t} {A = A} [Γ] ⊢Δ [σ] [A] [t]
consSubstSEq [Γ] ⊢Δ [σ] [σ≡σ'] [A] [t] =
  [σ≡σ'] , reflEqTerm (proj₁ ([A] ⊢Δ [σ])) [t]

wkSubstS : ∀ {ρ σ Γ Δ Δ'} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
           ([ρ] : ρ ∷ Δ ⊆ Δ')
           ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
         → Δ' ⊩ₛ wkSubst ρ σ ∷ Γ / [Γ] / ⊢Δ'
wkSubstS ε ⊢Δ ⊢Δ' ρ [σ] = tt
wkSubstS {σ = σ} {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ' ρ [σ] =
  let [tailσ] = wkSubstS [Γ] ⊢Δ ⊢Δ' ρ (proj₁ [σ])
  in  [tailσ]
   ,  irrelevanceTerm' (wk-subst A)
        (LR.wk ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))))
        (proj₁ (x ⊢Δ' [tailσ]))
        (LR.wkTerm ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ]))

wkSubstSEq : ∀ {ρ σ σ' Γ Δ Δ'} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
             ([ρ] : ρ ∷ Δ ⊆ Δ')
             ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ'] : Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
           → Δ' ⊩ₛ wkSubst ρ σ ≡ wkSubst ρ σ' ∷ Γ / [Γ]
                / ⊢Δ' / wkSubstS [Γ] ⊢Δ ⊢Δ' [ρ] [σ]
wkSubstSEq ε ⊢Δ ⊢Δ' ρ [σ] [σ≡σ'] = tt
wkSubstSEq {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ' ρ [σ] [σ≡σ'] =
  wkSubstSEq [Γ] ⊢Δ ⊢Δ' ρ (proj₁ [σ]) (proj₁ [σ≡σ'])
  , irrelevanceEqTerm' (wk-subst A) (LR.wk ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))))
                            (proj₁ (x ⊢Δ' (wkSubstS [Γ] ⊢Δ ⊢Δ' ρ (proj₁ [σ]))))
                            (LR.wkEqTerm ρ ⊢Δ' (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ≡σ']))

wk1SubstS : ∀ {F σ Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
          → (Δ ∙ F) ⊩ₛ wk1Subst σ ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F)
wk1SubstS {F} {σ} {Γ} {Δ} [Γ] ⊢Δ ⊢F [σ] =
  wkSubstS [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ]

wk1SubstSEq : ∀ {F σ σ' Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
              (⊢F : Δ ⊢ F)
              ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
              ([σ≡σ'] : Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
            → (Δ ∙ F) ⊩ₛ wk1Subst σ ≡ wk1Subst σ' ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F) / wk1SubstS [Γ] ⊢Δ ⊢F [σ]
wk1SubstSEq {l} {F} {σ} {Γ} {Δ} [Γ] ⊢Δ ⊢F [σ] [σ≡σ'] =
  wkSubstSEq [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ] [σ≡σ']

liftSubstS : ∀ {l F σ Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
           → (Δ ∙ subst σ F) ⊩ₛ liftSubst σ ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ wellformed (proj₁ ([F] ⊢Δ [σ])))
liftSubstS {F = F} {σ = σ} {Δ = Δ} [Γ] ⊢Δ [F] [σ] =
  let ⊢F = wellformed (proj₁ ([F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = subst σ F} [Γ] ⊢Δ (wellformed (proj₁ ([F] ⊢Δ [σ]))) [σ]
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                                     (wk-subst F) here)
  in  [tailσ] , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [tailσ])) (var zero)
                        var0 (~-var var0)

liftSubstSEq : ∀ {l F σ σ' Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ'] : Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
           → (Δ ∙ subst σ F) ⊩ₛ liftSubst σ ≡ liftSubst σ' ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ wellformed (proj₁ ([F] ⊢Δ [σ])))
                             / liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
liftSubstSEq {F = F} {σ = σ} {σ' = σ'} {Δ = Δ} [Γ] ⊢Δ [F] [σ] [σ≡σ'] =
  let ⊢F = wellformed (proj₁ ([F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = subst σ F} [Γ] ⊢Δ (wellformed (proj₁ ([F] ⊢Δ [σ]))) [σ]
      [tailσ≡σ'] = wk1SubstSEq [Γ] ⊢Δ (wellformed (proj₁ ([F] ⊢Δ [σ]))) [σ] [σ≡σ']
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F)) (wk-subst F) here)
  in  [tailσ≡σ'] , neuEqTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [tailσ])) (var zero) (var zero)
                         var0 var0 (~-var var0)

mutual
  soundContext : ∀ {Γ} → ⊩ₛ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) =
    soundContext x ∙ wellformed (irrelevance' (idSubst-lemma₀ _)
                                             (proj₁ (x₁ (soundContext x)
                                                        (idSubstS x))))

  idSubstS : ∀ {Γ} ([Γ] : ⊩ₛ Γ) → Γ ⊩ₛ idSubst ∷ Γ / [Γ] / soundContext [Γ]
  idSubstS ε = tt
  idSubstS {Γ = Γ ∙ A} ([Γ] ∙ [A]) =
    let ⊢Γ = soundContext [Γ]
        ⊢Γ∙A = soundContext ([Γ] ∙ [A])
        ⊢Γ∙A' = ⊢Γ ∙ wellformed (proj₁ ([A] ⊢Γ (idSubstS [Γ])))
        [A]' = wk1SubstS {F = subst idSubst A} [Γ] ⊢Γ
                         (wellformed (proj₁ ([A] (soundContext [Γ])
                                                (idSubstS [Γ]))))
                         (idSubstS [Γ])
        [tailσ] = S.irrelevanceSubst' (PE.cong (_∙_ Γ) (idSubst-lemma₀ A))
                                      [Γ] [Γ] ⊢Γ∙A' ⊢Γ∙A [A]'
        var0 = var ⊢Γ∙A (PE.subst (λ x → 0 ∷ x ∈ (Γ ∙ A))
                                  (wk-subst A)
                                  (PE.subst (λ x → 0 ∷ wk1 (subst idSubst A)
                                                     ∈ (Γ ∙ x))
                                            (idSubst-lemma₀ A) here))
    in  [tailσ]
    ,   neuTerm (proj₁ ([A] ⊢Γ∙A [tailσ]))
                (var zero)
                var0 (~-var var0)

reflSubst : ∀ {σ Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
            ([σ] : Δ ⊩ₛ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩ₛ σ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ]
reflSubst ε ⊢Δ [σ] = tt
reflSubst ([Γ] ∙ x) ⊢Δ [σ] =
  reflSubst [Γ] ⊢Δ (proj₁ [σ]) , reflEqTerm (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ])

reflIdSubst : ∀ {Γ} ([Γ] : ⊩ₛ Γ)
            → Γ ⊩ₛ idSubst ≡ idSubst ∷ Γ / [Γ] / soundContext [Γ] / idSubstS [Γ]
reflIdSubst [Γ] = reflSubst [Γ] (soundContext [Γ]) (idSubstS [Γ])

symS : ∀ {σ σ' Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
       ([σ]  : Δ ⊩ₛ σ  ∷ Γ / [Γ] / ⊢Δ)
       ([σ'] : Δ ⊩ₛ σ' ∷ Γ / [Γ] / ⊢Δ)
     → Δ ⊩ₛ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
     → Δ ⊩ₛ σ' ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ']
symS ε ⊢Δ [σ] [σ'] [σ≡σ'] = tt
symS ([Γ] ∙ x) ⊢Δ [σ] [σ'] [σ≡σ'] =
  symS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ']) (proj₁ [σ≡σ'])
  , let [σA]           = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ'A]          = proj₁ (x ⊢Δ (proj₁ [σ']))
        [σA≡σ'A]       = (proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ']) (proj₁ [σ≡σ'])
        [headσ'≡headσ] = symEqTerm [σA] (proj₂ [σ≡σ'])
    in  convEqTerm₁ [σA] [σ'A] [σA≡σ'A] [headσ'≡headσ]

transS : ∀ {σ σ' σ'' Γ Δ} ([Γ] : ⊩ₛ Γ) (⊢Δ : ⊢ Δ)
         ([σ]   : Δ ⊩ₛ σ   ∷ Γ / [Γ] / ⊢Δ)
         ([σ']  : Δ ⊩ₛ σ'  ∷ Γ / [Γ] / ⊢Δ)
         ([σ''] : Δ ⊩ₛ σ'' ∷ Γ / [Γ] / ⊢Δ)
       → Δ ⊩ₛ σ  ≡ σ'  ∷ Γ / [Γ] / ⊢Δ / [σ]
       → Δ ⊩ₛ σ' ≡ σ'' ∷ Γ / [Γ] / ⊢Δ / [σ']
       → Δ ⊩ₛ σ  ≡ σ'' ∷ Γ / [Γ] / ⊢Δ / [σ]
transS ε ⊢Δ [σ] [σ'] [σ''] [σ≡σ'] [σ'≡σ''] = tt
transS ([Γ] ∙ x) ⊢Δ [σ] [σ'] [σ''] [σ≡σ'] [σ'≡σ''] =
  transS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ']) (proj₁ [σ''])
         (proj₁ [σ≡σ']) (proj₁ [σ'≡σ''])
  , let [σA]   = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ'A]  = proj₁ (x ⊢Δ (proj₁ [σ']))
        [σ''A] = proj₁ (x ⊢Δ (proj₁ [σ'']))
        [σ'≡σ'']' = convEqTerm₂ [σA] [σ'A]
                                ((proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ'])
                                        (proj₁ [σ≡σ'])) (proj₂ [σ'≡σ''])
    in  transEqTerm [σA] (proj₂ [σ≡σ']) [σ'≡σ'']'
