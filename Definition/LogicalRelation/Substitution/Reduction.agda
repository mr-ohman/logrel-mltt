module Definition.LogicalRelation.Substitution.Reduction where

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


redSubstTermₛ : ∀ {A t u l Γ}
              → ([Γ] : ⊩ₛ Γ)
              → Γ ⊩ₛ t ⇒ u ∷ A / [Γ]
              → ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ₛ⟨ l ⟩t u ∷ A / [Γ] / [A]
              → Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
              × Γ ⊩ₛ⟨ l ⟩t' t ≡ u ∷ A / [Γ] / [A]
redSubstTermₛ [Γ] t⇒u [A] [u] =
  (λ ⊢Δ [σ] →
     let [σA] = proj₁ ([A] ⊢Δ [σ])
         [σt] , [σt≡σu] = redSubstTerm (t⇒u ⊢Δ [σ])
                                       (proj₁ ([A] ⊢Δ [σ]))
                                       (proj₁ ([u] ⊢Δ [σ]))
     in  [σt]
     ,   (λ [σ'] [σ≡σ'] →
            let [σ'A] = proj₁ ([A] ⊢Δ [σ'])
                [σA≡σ'A] = proj₂ ([A] ⊢Δ [σ]) [σ'] [σ≡σ']
                [σ't] , [σ't≡σ'u] = redSubstTerm (t⇒u ⊢Δ [σ'])
                                                 (proj₁ ([A] ⊢Δ [σ']))
                                                 (proj₁ ([u] ⊢Δ [σ']))
            in  transEqTerm [σA] [σt≡σu]
                            (transEqTerm [σA] ((proj₂ ([u] ⊢Δ [σ])) [σ'] [σ≡σ'])
                                         (convEqTerm₂ [σA] [σ'A] [σA≡σ'A]
                                                      (symEqTerm [σ'A] [σ't≡σ'u])))))
  , (λ ⊢Δ [σ] → proj₂ (redSubstTerm (t⇒u ⊢Δ [σ])
                                    (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₁ ([u] ⊢Δ [σ]))))
