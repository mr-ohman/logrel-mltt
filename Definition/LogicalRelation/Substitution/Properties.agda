{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Properties {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Irrelevance
     using (irrelevanceSubst′)
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening as LR

open import Tools.Fin
open import Tools.Nat
open import Tools.Unit
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    k m n : Nat
    Γ : Con Term n
    σ σ′ : Subst m n
    ρ : Wk k n

-- Valid substitutions are well-formed
wellformedSubst : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
      → Δ ⊢ˢ σ ∷ Γ
wellformedSubst ε ⊢Δ [σ] = id
wellformedSubst ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) =
  wellformedSubst [Γ] ⊢Δ [tailσ]
  , escapeTerm (proj₁ ([A] ⊢Δ [tailσ])) [headσ]

-- Valid substitution equality is well-formed
wellformedSubstEq : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
      ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
wellformedSubstEq ε ⊢Δ [σ] [σ≡σ′] = id
wellformedSubstEq ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) ([tailσ≡σ′] , [headσ≡σ′]) =
  wellformedSubstEq [Γ] ⊢Δ [tailσ] [tailσ≡σ′]
  , ≅ₜ-eq (escapeTermEq (proj₁ ([A] ⊢Δ [tailσ])) [headσ≡σ′])

-- Extend a valid substitution with a term
consSubstS : ∀ {l t A Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
           ([t] : Δ ⊩⟨ l ⟩ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ]))
         → Δ ⊩ˢ consSubst σ t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
consSubstS [Γ] ⊢Δ [σ] [A] [t] = [σ] , [t]

-- Extend a valid substitution equality with a term
consSubstSEq : ∀ {l t A Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([σ]    : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([t] : Δ ⊩⟨ l ⟩ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ]))
           → Δ ⊩ˢ consSubst σ t ≡ consSubst σ′ t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
               / consSubstS {t = t} {A = A} [Γ] ⊢Δ [σ] [A] [t]
consSubstSEq [Γ] ⊢Δ [σ] [σ≡σ′] [A] [t] =
  [σ≡σ′] , reflEqTerm (proj₁ ([A] ⊢Δ [σ])) [t]

-- Weakening of valid substitutions
wkSubstS : ∀ {Γ Δ Δ′} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
         → Δ′ ⊩ˢ ρ •ₛ σ ∷ Γ / [Γ] / ⊢Δ′
wkSubstS ε ⊢Δ ⊢Δ′ ρ [σ] = tt
wkSubstS {σ = σ} {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] =
  let [tailσ] = wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ])
  in  [tailσ]
   ,  irrelevanceTerm′ (wk-subst A)
        (LR.wk ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))))
        (proj₁ (x ⊢Δ′ [tailσ]))
        (LR.wkTerm ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ]))

-- Weakening of valid substitution equality
wkSubstSEq : ∀ {Γ Δ Δ′} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([ρ] : ρ ∷ Δ′ ⊆ Δ)
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
           → Δ′ ⊩ˢ ρ •ₛ σ ≡ ρ •ₛ σ′ ∷ Γ / [Γ]
                / ⊢Δ′ / wkSubstS [Γ] ⊢Δ ⊢Δ′ [ρ] [σ]
wkSubstSEq ε ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] = tt
wkSubstSEq {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] =
  wkSubstSEq [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]) (proj₁ [σ≡σ′])
  , irrelevanceEqTerm′ (wk-subst A) (LR.wk ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))))
                            (proj₁ (x ⊢Δ′ (wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]))))
                            (LR.wkEqTerm ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ≡σ′]))

-- Weaken a valid substitution by one type
wk1SubstS : ∀ {F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → (Δ ∙ F) ⊩ˢ wk1Subst σ ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F)
wk1SubstS {F} {σ} {Γ} {Δ} [Γ] ⊢Δ ⊢F [σ] =
  wkSubstS [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

-- Weaken a valid substitution equality by one type
wk1SubstSEq : ∀ {F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
              (⊢F : Δ ⊢ F)
              ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
              ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
            → (Δ ∙ F) ⊩ˢ wk1Subst σ ≡ wk1Subst σ′ ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F) / wk1SubstS [Γ] ⊢Δ ⊢F [σ]
wk1SubstSEq {l} {F} {σ} {Γ} {Δ} [Γ] ⊢Δ ⊢F [σ] [σ≡σ′] =
  wkSubstSEq [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ] [σ≡σ′]

-- Lift a valid substitution
liftSubstS : ∀ {l F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → (Δ ∙ subst σ F) ⊩ˢ liftSubst σ ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ escape (proj₁ ([F] ⊢Δ [σ])))
liftSubstS {σ = σ} {F = F} {Δ = Δ} [Γ] ⊢Δ [F] [σ] =
  let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = subst σ F} [Γ] ⊢Δ (escape (proj₁ ([F] ⊢Δ [σ]))) [σ]
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ subst σ F))
                                     (wk-subst F) here)
  in  [tailσ] , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [tailσ])) (var x0)
                        var0 (~-var var0)

-- Lift a valid substitution equality
liftSubstSEq : ∀ {l F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
           → (Δ ∙ subst σ F) ⊩ˢ liftSubst σ ≡ liftSubst σ′ ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ escape (proj₁ ([F] ⊢Δ [σ])))
                             / liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
liftSubstSEq {σ = σ} {σ′ = σ′} {F = F} {Δ = Δ} [Γ] ⊢Δ [F] [σ] [σ≡σ′] =
  let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = subst σ F} [Γ] ⊢Δ (escape (proj₁ ([F] ⊢Δ [σ]))) [σ]
      [tailσ≡σ′] = wk1SubstSEq [Γ] ⊢Δ (escape (proj₁ ([F] ⊢Δ [σ]))) [σ] [σ≡σ′]
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ subst σ F)) (wk-subst F) here)
  in  [tailσ≡σ′] , neuEqTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [tailσ])) (var x0) (var x0)
                         var0 var0 (~-var var0)

mutual
  -- Valid contexts are well-formed
  soundContext : ⊩ᵛ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) =
    soundContext x ∙ escape (irrelevance′ (subst-id _)
                                             (proj₁ (x₁ (soundContext x)
                                                        (idSubstS x))))

  -- From a valid context we can constuct a valid identity substitution
  idSubstS : ([Γ] : ⊩ᵛ Γ) → Γ ⊩ˢ idSubst ∷ Γ / [Γ] / soundContext [Γ]
  idSubstS ε = tt
  idSubstS {Γ = Γ ∙ A} ([Γ] ∙ [A]) =
    let ⊢Γ = soundContext [Γ]
        ⊢Γ∙A = soundContext ([Γ] ∙ [A])
        ⊢Γ∙A′ = ⊢Γ ∙ escape (proj₁ ([A] ⊢Γ (idSubstS [Γ])))
        [A]′ = wk1SubstS {F = subst idSubst A} [Γ] ⊢Γ
                         (escape (proj₁ ([A] (soundContext [Γ])
                                                (idSubstS [Γ]))))
                         (idSubstS [Γ])
        [tailσ] = irrelevanceSubst′ (PE.cong (_∙_ Γ) (subst-id A))
                                    [Γ] [Γ] ⊢Γ∙A′ ⊢Γ∙A [A]′
        var0 = var ⊢Γ∙A (PE.subst (λ x → x0 ∷ x ∈ (Γ ∙ A))
                                  (wk-subst A)
                                  (PE.subst (λ x → x0 ∷ wk1 (subst idSubst A)
                                                     ∈ (Γ ∙ x))
                                            (subst-id A) here))
    in  [tailσ]
    ,   neuTerm (proj₁ ([A] ⊢Γ∙A [tailσ]))
                (var x0)
                var0 (~-var var0)

-- Reflexivity valid substitutions
reflSubst : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
            ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩ˢ σ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ]
reflSubst ε ⊢Δ [σ] = tt
reflSubst ([Γ] ∙ x) ⊢Δ [σ] =
  reflSubst [Γ] ⊢Δ (proj₁ [σ]) , reflEqTerm (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ])

-- Reflexivity of valid identity substitution
reflIdSubst : ([Γ] : ⊩ᵛ Γ)
            → Γ ⊩ˢ idSubst ≡ idSubst ∷ Γ / [Γ] / soundContext [Γ] / idSubstS [Γ]
reflIdSubst [Γ] = reflSubst [Γ] (soundContext [Γ]) (idSubstS [Γ])

-- Symmetry of valid substitution
symS : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
       ([σ]  : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
       ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
     → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
     → Δ ⊩ˢ σ′ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ′]
symS ε ⊢Δ [σ] [σ′] [σ≡σ′] = tt
symS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ≡σ′] =
  symS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ≡σ′])
  , let [σA]           = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ′A]          = proj₁ (x ⊢Δ (proj₁ [σ′]))
        [σA≡σ′A]       = (proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′]) (proj₁ [σ≡σ′])
        [headσ′≡headσ] = symEqTerm [σA] (proj₂ [σ≡σ′])
    in  convEqTerm₁ [σA] [σ′A] [σA≡σ′A] [headσ′≡headσ]

-- Transitivity of valid substitution
transS : ∀ {σ″ Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
         ([σ]   : Δ ⊩ˢ σ   ∷ Γ / [Γ] / ⊢Δ)
         ([σ′]  : Δ ⊩ˢ σ′  ∷ Γ / [Γ] / ⊢Δ)
         ([σ″] : Δ ⊩ˢ σ″ ∷ Γ / [Γ] / ⊢Δ)
       → Δ ⊩ˢ σ  ≡ σ′  ∷ Γ / [Γ] / ⊢Δ / [σ]
       → Δ ⊩ˢ σ′ ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ′]
       → Δ ⊩ˢ σ  ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ]
transS ε ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] = tt
transS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] =
  transS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ″])
         (proj₁ [σ≡σ′]) (proj₁ [σ′≡σ″])
  , let [σA]   = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ′A]  = proj₁ (x ⊢Δ (proj₁ [σ′]))
        [σ″A] = proj₁ (x ⊢Δ (proj₁ [σ″]))
        [σ′≡σ″]′ = convEqTerm₂ [σA] [σ′A]
                                ((proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′])
                                        (proj₁ [σ≡σ′])) (proj₂ [σ′≡σ″])
    in  transEqTerm [σA] (proj₂ [σ≡σ′]) [σ′≡σ″]′
