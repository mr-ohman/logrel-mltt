module Definition.LogicalRelation.Substitution.Irrelevance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
import Definition.LogicalRelation.Irrelevance as LR
open import Definition.LogicalRelation.Substitution

open import Tools.Context

open import Data.Product
open import Data.Unit


irrelevanceSubst : ∀ {l l' σ Γ Δ}
                   ([Γ]  : ⊩ₛ⟨ l  ⟩ Γ)
                   ([Γ]' : ⊩ₛ⟨ l' ⟩ Γ)
                   (⊢Δ ⊢Δ' : ⊢ Δ)
                 → Δ ⊩ₛ⟨ l  ⟩ σ ∷ Γ / [Γ]  / ⊢Δ
                 → Δ ⊩ₛ⟨ l' ⟩ σ ∷ Γ / [Γ]' / ⊢Δ'
irrelevanceSubst ε ε ⊢Δ ⊢Δ' [σ] = tt
irrelevanceSubst ([Γ] ∙ [A]) ([Γ]' ∙ [A]') ⊢Δ ⊢Δ' ([tailσ] , [headσ]) =
  let [tailσ]' = irrelevanceSubst [Γ] [Γ]' ⊢Δ ⊢Δ' [tailσ]
  in  [tailσ]'
  ,   LR.irrelevanceTerm (proj₁ ([A] ⊢Δ [tailσ]))
                            (proj₁ ([A]' ⊢Δ' [tailσ]'))
                            [headσ]

irrelevanceSubstEq : ∀ {l l' σ σ' Γ Δ}
                     ([Γ]  : ⊩ₛ⟨ l  ⟩ Γ)
                     ([Γ]' : ⊩ₛ⟨ l' ⟩ Γ)
                     (⊢Δ ⊢Δ' : ⊢ Δ)
                     ([σ]  : Δ ⊩ₛ⟨ l  ⟩ σ ∷ Γ / [Γ]  / ⊢Δ)
                     ([σ]' : Δ ⊩ₛ⟨ l' ⟩ σ ∷ Γ / [Γ]' / ⊢Δ')
                   → Δ ⊩ₛ⟨ l  ⟩ σ ≡ σ' ∷ Γ / [Γ]  / ⊢Δ  / [σ]
                   → Δ ⊩ₛ⟨ l' ⟩ σ ≡ σ' ∷ Γ / [Γ]' / ⊢Δ' / [σ]'
irrelevanceSubstEq ε ε ⊢Δ ⊢Δ' [σ] [σ]' [σ≡σ'] = tt
irrelevanceSubstEq ([Γ] ∙ [A]) ([Γ]' ∙ [A]') ⊢Δ ⊢Δ' [σ] [σ]' [σ≡σ'] =
  irrelevanceSubstEq [Γ] [Γ]' ⊢Δ ⊢Δ' (proj₁ [σ]) (proj₁ [σ]') (proj₁ [σ≡σ'])
  , LR.irrelevanceEqTerm (proj₁ ([A] ⊢Δ  (proj₁ [σ])))
                            (proj₁ ([A]' ⊢Δ' (proj₁ [σ]')))
                            (proj₂ [σ≡σ'])

irrelevance : ∀ {l A Γ}
              ([Γ] [Γ]' : ⊩ₛ⟨ l  ⟩ Γ)
            → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
            → Γ ⊩ₛ⟨ l ⟩ A / [Γ]'
irrelevance [Γ] [Γ]' [A] ⊢Δ [σ] =
  let [σ]' = irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  proj₁ ([A] ⊢Δ [σ]')
   ,  λ [σ≡σ'] → proj₂ ([A] ⊢Δ [σ]')
                       (irrelevanceSubstEq [Γ]' [Γ] ⊢Δ ⊢Δ [σ] [σ]' [σ≡σ'])

open import Definition.LogicalRelation.Properties

irrelevanceLift : ∀ {l A F H Γ}
              ([Γ] : ⊩ₛ⟨ l ⟩ Γ)
              ([F] : Γ ⊩ₛ⟨ l ⟩ F / [Γ])
              ([H] : Γ ⊩ₛ⟨ l ⟩ H / [Γ])
              ([F≡H] : Γ ⊩ₛ⟨ l ⟩ F ≡ H / [Γ] / [F])
            → Γ ∙ F ⊩ₛ⟨ l ⟩ A / [Γ] ∙ [F]
            → Γ ∙ H ⊩ₛ⟨ l ⟩ A / [Γ] ∙ [H]
irrelevanceLift [Γ] [F] [H] [F≡H] [A] ⊢Δ ([tailσ] , [headσ]) =
  let [σ]' = [tailσ] , convTerm₂ (proj₁ ([F] ⊢Δ [tailσ])) (proj₁ ([H] ⊢Δ [tailσ])) ([F≡H] ⊢Δ [tailσ]) [headσ]
  in  proj₁ ([A] ⊢Δ [σ]')
  ,   (λ x → proj₂ ([A] ⊢Δ [σ]') (proj₁ x , convEqTerm₂ (proj₁ ([F] ⊢Δ [tailσ])) (proj₁ ([H] ⊢Δ [tailσ])) ([F≡H] ⊢Δ [tailσ]) (proj₂ x)))

irrelevanceEq : ∀ {l l' A B Γ}
                ([Γ]  : ⊩ₛ⟨ l  ⟩ Γ)
                ([Γ]' : ⊩ₛ⟨ l' ⟩ Γ)
                ([A]  : Γ ⊩ₛ⟨ l  ⟩ A / [Γ])
                ([A]' : Γ ⊩ₛ⟨ l' ⟩ A / [Γ]')
              → Γ ⊩ₛ⟨ l  ⟩ A ≡ B / [Γ]  / [A]
              → Γ ⊩ₛ⟨ l' ⟩ A ≡ B / [Γ]' / [A]'
irrelevanceEq [Γ] [Γ]' [A] [A]' [A≡B] ⊢Δ [σ] =
  let [σ]' = irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]
  in  LR.irrelevanceEq (proj₁ ([A] ⊢Δ [σ]')) (proj₁ ([A]' ⊢Δ [σ])) ([A≡B] ⊢Δ [σ]')

irrelevanceTerm : ∀ {l l' A t Γ}
                  ([Γ]  : ⊩ₛ⟨ l  ⟩ Γ)
                  ([Γ]' : ⊩ₛ⟨ l' ⟩ Γ)
                  ([A]  : Γ ⊩ₛ⟨ l  ⟩ A / [Γ])
                  ([A]' : Γ ⊩ₛ⟨ l' ⟩ A / [Γ]')
                → Γ ⊩ₛ⟨ l  ⟩t t ∷ A / [Γ]  / [A]
                → Γ ⊩ₛ⟨ l' ⟩t t ∷ A / [Γ]' / [A]'
irrelevanceTerm [Γ] [Γ]' [A] [A]' [t] ⊢Δ [σ]' =
  let [σ]   = irrelevanceSubst [Γ]' [Γ] ⊢Δ ⊢Δ [σ]'
      [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]' = proj₁ ([A]' ⊢Δ [σ]')
  in  LR.irrelevanceTerm [σA] [σA]' (proj₁ ([t] ⊢Δ [σ]))
   ,  λ x → LR.irrelevanceEqTerm [σA] [σA]' ((proj₂ ([t] ⊢Δ [σ]))
            (irrelevanceSubstEq [Γ]' [Γ] ⊢Δ ⊢Δ [σ]' [σ] x))


-- irrelevanceTermEq
