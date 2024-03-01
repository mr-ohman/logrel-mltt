{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Fundamental {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Fin
open import Tools.Product
open import Tools.Unit
open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ σ′ : Subst m n

-- move to where it belongs
⊩ᵛ-sym : ∀ {n} {Γ : Con Term n} {A B l}
           ([Γ] : ⊩ᵛ Γ)
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
           ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
         → Γ ⊩ᵛ⟨ l ⟩ B ≡ A / [Γ] / [B]
⊩ᵛ-sym {n = n} {Γ} {A} {B} {l} [Γ] [A] [B] [A≡B] {k} {Δ} {σ} ⊢Δ [σ] =
  symEq {A = subst σ A} {B = subst σ B}
        (proj₁ ([A] ⊢Δ [σ]))
        (proj₁ ([B] ⊢Δ [σ]))
        ([A≡B] ⊢Δ [σ])

mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕⱼ x) = valid x , ℕᵛ (valid x)
  fundamental (Emptyⱼ x) = valid x , Emptyᵛ (valid x)
  fundamental (Unitⱼ x) = valid x , Unitᵛ (valid x)
  fundamental (Uⱼ x) = valid x , Uᵛ (valid x)
  fundamental (Πⱼ_▹_ {F} {G} ⊢F ⊢G)
    with fundamental ⊢F | fundamental ⊢G
  fundamental (Πⱼ_▹_ {F} {G} ⊢F ⊢G)
    | [Γ] , [F]
    | [Γ∙F] , [G] =
      [Γ] , Πᵛ {F = F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (Σⱼ_▹_ {F} {G} ⊢F ⊢G)
    with fundamental ⊢F | fundamental ⊢G
  fundamental (Σⱼ_▹_ {F} {G} ⊢F ⊢G)
    | [Γ] , [F]
    | [Γ∙F] , [G] =
      [Γ] , Σᵛ {F = F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (_∪ⱼ_ {A} {B} ⊢A ⊢B)
    with fundamental ⊢A | fundamental ⊢B
  fundamental (_∪ⱼ_ {A} {B} ⊢A ⊢B)
    | [Γ] , [A]
    | [Δ] , [B] =
      [Γ] , ∪ᵛ {F = A} {B} [Γ] [A] (S.irrelevance {A = B} [Δ] [Γ] [B])
  fundamental (∥_∥ⱼ {A} ⊢A)
    with fundamental ⊢A
  fundamental (∥_∥ⱼ {A} ⊢A)
    | [Γ] , [A] =
      [Γ] , ∥ᵛ {F = A} [Γ] [A]
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , univᵛ {A = A} [Γ] [U] [A]

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀ {A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ᵛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = univᵛ {A = A} [Γ] [U] [t]
        [B] = univᵛ {A = B} [Γ] [U] [u]
    in  [Γ] , [A] , [B]
    ,   (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ]))
                             (proj₁ ([A] ⊢Δ [σ]))
                             ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) =
    let [Γ] , [B] = fundamental D
    in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] =
    [Γ] , [A] , [B]
        , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ]))
                            (proj₁ ([A] ⊢Δ [σ]))
                            ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans {A} {B₁} {B} A≡B₁ B₁≡B)
    with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {A} {B₁} {B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁]
    | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
      [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
          , (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                           (proj₁ ([B] ⊢Δ [σ]′)) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ]′))
                                          (proj₁ ([B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]′)))
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [Γ] , [F] , [H] , [F≡H]
    | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Πᵛ {F = F} {G} [Γ] [F] [G]′
      ,   Πᵛ {F = H} {E} [Γ] [H] [E]′
      ,   Π-congᵛ {F = F} {G} {H} {E} [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′
  fundamentalEq (Σ-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Σ-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [Γ] , [F] , [H] , [F≡H]
    | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Σᵛ {F = F} {G} [Γ] [F] [G]′
      ,   Σᵛ {F = H} {E} [Γ] [H] [E]′
      ,   Σ-congᵛ {F = F} {G} {H} {E} [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′
  fundamentalEq (∪-cong {A} {B} {C} {D} A≡B C≡D)
    with fundamentalEq A≡B | fundamentalEq C≡D
  fundamentalEq (∪-cong {A} {B} {C} {D} A≡B C≡D)
    | [Γ]  , [A] , [B] , [A≡B]
    | [Γ]₁ , [C] , [D] , [C≡D] =
      let [C]′   = S.irrelevance {A = C} [Γ]₁ [Γ] [C]
          [D]′   = S.irrelevance {A = D} [Γ]₁ [Γ] [D]
          [C≡D]′ = S.irrelevanceEq {A = C} {B = D} [Γ]₁ [Γ] [C] [C]′ [C≡D]
      in  [Γ]
      ,   ∪ᵛ {F = A} {C} [Γ] [A] [C]′
      ,   ∪ᵛ {F = B} {D} [Γ] [B] [D]′
      ,   ∪-congᵛ {F = A} {C} {B} {D} [Γ] [A] [C]′ [B] [D]′ [A≡B] [C≡D]′
  fundamentalEq (∥-cong {A} {B} A≡B)
    with fundamentalEq A≡B
  fundamentalEq (∥-cong {A} {B} A≡B)
    | [Γ] , [A] , [B] , [A≡B] =
      [Γ]
      , ∥ᵛ {F = A} [Γ] [A]
      , ∥ᵛ {F = B} [Γ] [B]
      , ∥-congᵛ {F = A} {B} [Γ] [A] [B] [A≡B]

  -- Fundamental theorem for variables.
  fundamentalVar : ∀ {A x}
                 → x ∷ A ∈ Γ
                 → ([Γ] : ⊩ᵛ Γ)
                 → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
                 → Γ ⊩ᵛ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
  fundamentalVar here (_∙_ {A = A} {l = l} [Γ] [A]) =
    (λ ⊢Δ [σ] →
       let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
           [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA′] (proj₂ ([A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
             [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₂ [σ])
         ,   (λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (subst-wk A))
                                                 [σA] [σA′] (proj₂ [σ≡σ′])))
  fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (λ ⊢Δ [σ] →
       let [h]   = proj₁ (fundamentalVar h [Γ]) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA′]
                              (proj₂ [h] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
             [h′] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₁ [h′])
         ,   (λ [σ′] [σ≡σ′] →
                irrelevanceEqTerm′ (PE.sym (subst-wk A)) [σA] [σA′]
                                   (proj₂ [h′] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ x) = valid x , Uᵛ (valid x) , ℕᵗᵛ (valid x)
  fundamentalTerm (Emptyⱼ x) = valid x , Uᵛ (valid x) , Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ x) = valid x , Uᵛ (valid x) , Unitᵗᵛ (valid x)
  fundamentalTerm (Πⱼ_▹_ {F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁
                                  (λ {_} {Δ} {σ} → [U]′ {Δ = Δ} {σ}) [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Π F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
                          (Πᵗᵛ {F = F} {G} [Γ] [F] (λ {_} {Δ} {σ} → [U]′ {Δ = Δ} {σ})
                               [F]ₜ′ [G]ₜ′)
  fundamentalTerm (Σⱼ_▹_ {F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁
                                  (λ {_} {Δ} {σ} → [U]′ {Δ = Δ} {σ}) [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Σ F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
                          (Σᵗᵛ {F = F} {G} [Γ] [F] (λ {_} {Δ} {σ} → [U]′ {Δ = Δ} {σ})
                               [F]ₜ′ [G]ₜ′)
  fundamentalTerm (_∪ⱼ_ {A} {B} ⊢A ⊢B)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B
  ... | [Γ]  , [U]  , [A]ₜ
      | [Γ]₁ , [U]₁ , [B]ₜ =
    let [A]ₜ′ = S.irrelevanceTerm {A = U} {t = A} [Γ] [Γ] [U] (Uᵛ [Γ]) [A]ₜ
        [B]ₜ′ = S.irrelevanceTerm {A = U} {t = B} [Γ]₁ [Γ] [U]₁ (Uᵛ [Γ]) [B]ₜ
    in [Γ] , [U]
     , S.irrelevanceTerm {A = U} {t = A ∪ B} [Γ] [Γ] (Uᵛ [Γ]) [U]
                         (∪ᵗᵛ {F = A} {B} [Γ] [A]ₜ′ [B]ₜ′)
  fundamentalTerm (∥_∥ⱼ {A} ⊢A)
    with fundamentalTerm ⊢A
  ... | [Γ]  , [U]  , [A]ₜ =
    let [A]ₜ′ = S.irrelevanceTerm {A = U} {t = A} [Γ] [Γ] [U] (Uᵛ [Γ]) [A]ₜ
    in [Γ] , [U]
     , S.irrelevanceTerm {A = U} {t = ∥ A ∥} [Γ] [Γ] (Uᵛ [Γ]) [U]
                         (∥ᵗᵛ {F = A} [Γ] [A]ₜ′)
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lamⱼ {F} {G} {t} ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πᵛ {F = F} {G} [Γ] [F] [G]′
    ,   lamᵛ {F = F} {G} {t} [Γ] [F] [G]′ [t]′
  fundamentalTerm (_∘ⱼ_ {g} {a} {F} {G} Dt Du)
    with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [t]′ = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substSΠ {F = F} {G} {a} BΠ [Γ]₁ [F] [ΠFG]′ [u]
        [t∘u] = appᵛ {F = F} {G} {g} {a} [Γ]₁ [F] [ΠFG]′ [t]′ [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (prodⱼ {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u) with
    fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G] | [Γ]₂ , [Gt] , [u] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [u]′ = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ] [Gt] (substS {F = F} {G} [Γ] [F] [G]′ [t]) [u]
    in  [Γ] , Σᵛ {F = F} {G} [Γ] [F] [G]′ , prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G]′ [t] [u]′
  fundamentalTerm (fstⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ F ▹ G} {t = t} [Γ]₂ [Γ]
                                [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G]) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]
    in  [Γ] , [F] , [fst]
  fundamentalTerm (sndⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ F ▹ G} {t = t} [Γ]₂ [Γ]
                                [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G]) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} [Γ] [F] [G] [t]
    in  [Γ] , [Gfst] , [snd]
  fundamentalTerm (injlⱼ {A} {B} {t} ⊢B ⊢t)
    with fundamentalTerm ⊢t | fundamental ⊢B
  ... | [Γ] , [A] , [t] | [Γ]₁ , [B] =
    let [B]′ = S.irrelevance {A = B} [Γ]₁ [Γ] [B]
    in [Γ] , ∪ᵛ {F = A} {B} [Γ] [A] [B]′ ,
       injlᵛ {A = A} {B} {t} [Γ] [A] [B]′ [t]
  fundamentalTerm (injrⱼ {A} {B} {t} ⊢A ⊢t)
    with fundamentalTerm ⊢t | fundamental ⊢A
  ... | [Γ] , [B] , [t] | [Γ]₁ , [A] =
    let [A]′ = S.irrelevance {A = A} [Γ]₁ [Γ] [A]
    in [Γ] , ∪ᵛ {F = A} {B} [Γ] [A]′ [B] ,
       injrᵛ {A = A} {B} {t} [Γ] [A]′ [B] [t]
  fundamentalTerm (casesⱼ {A} {B} {C} {t} {u} {v} ⊢t ⊢u ⊢v ⊢C)
    with fundamentalTerm ⊢t | fundamentalTerm ⊢u | fundamentalTerm ⊢v | fundamental ⊢C
  ... | [Γ] , [∪AB] , [t] | [Γ]₁ , [AC] , [u] | [Γ]₂ , [BC] , [v] | [Γ]₃ , [C] =
    let [C]₁  = S.irrelevance {A = C} [Γ]₃ [Γ] [C]
        [AC]₁ = S.irrelevance {A = A ▹▹ C} [Γ]₁ [Γ] [AC]
        [BC]₁ = S.irrelevance {A = B ▹▹ C} [Γ]₂ [Γ] [BC]
        [A]₁  = ⊩ᵛ▹▹ₗ {A = A} {B = C} [Γ] [AC]₁
        [B]₁  = ⊩ᵛ▹▹ₗ {A = B} {B = C} [Γ] [BC]₁
        [t]₁  = S.irrelevanceTerm {A = A ∪ B} {t = t} [Γ] [Γ] [∪AB] (∪ᵛ {F = A} {B} [Γ] [A]₁ [B]₁) [t]
        [u]₁  = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₁ [Γ] [AC] (▹▹ᵛ {F = A} {C} [Γ] [A]₁ [C]₁) [u]
        [v]₁  = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₂ [Γ] [BC] (▹▹ᵛ {F = B} {C} [Γ] [B]₁ [C]₁) [v]
    in [Γ] , [C]₁ ,
       casesᵛ {A = A} {B} {C} {t = t} {u = u} {v = v} [Γ] [A]₁ [B]₁ [C]₁ [t]₁ [u]₁ [v]₁
  fundamentalTerm (∥ᵢⱼ {A} {a} ⊢a)
    with fundamentalTerm ⊢a
  ... | [Γ] , [A] , [a] =
    [Γ] ,
    ∥ᵛ {F = A} [Γ] [A] ,
    ∥ᵢᵛ {A = A} {a} [Γ] [A] [a]
  --
  fundamentalTerm {Γ = Γ} (∥ₑⱼ {A} {B} {a} {f} ⊢a ⊢f ⊢B)
    with fundamentalTerm ⊢a | fundamentalTerm ⊢f | fundamental ⊢B
  ... | [Γ] , [∥A∥] , [a] | [Γ]₁ , [AB] , [f] | [Γ]₂ , [B] =
    let [B]₁   = S.irrelevance {A = B} [Γ]₂ [Γ] [B]
        [AB]₁  = S.irrelevance {A = A ▹▹ ∥ B ∥} [Γ]₁ [Γ] [AB]
        [A]₁   = ⊩ᵛ▹▹ₗ {A = A} {B = ∥ B ∥} [Γ] [AB]₁
        [∥B∥]₁ = ⊩ᵛ∥ {Γ = Γ} {A = B} [Γ] [B]₁
        [a]₁   = S.irrelevanceTerm {A = ∥ A ∥} {t = a} [Γ] [Γ] [∥A∥] (∥ᵛ {F = A} [Γ] [A]₁) [a]
        [f]₁   = S.irrelevanceTerm {A = A ▹▹ ∥ B ∥} {t = f} [Γ]₁ [Γ] [AB] (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A]₁ [∥B∥]₁) [f]
    in [Γ] , [∥B∥]₁ ,
       ∥ₑᵛ {A = A} {B} {a = a} {f = f} [Γ] [A]₁ [B]₁ [∥B∥]₁ [a]₁ [f]₁
  --
  fundamentalTerm (zeroⱼ x) = valid x , ℕᵛ (valid x) , zeroᵛ {l = ¹} (valid x)
  fundamentalTerm (sucⱼ {n} t) with fundamentalTerm t
  fundamentalTerm (sucⱼ {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucᵛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrecⱼ {G} {s} {z} {n} ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let sType = Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
        [Γ]′ = [Γ]₃
        [G]′ = S.irrelevance {A = G} [Γ] ([Γ]′ ∙ [ℕ]) [G]
        [G₀]′ = S.irrelevance {A = G [ zero ]} [Γ]₁ [Γ]′ [G₀]
        [G₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [G₊]
        [Gₙ]′ = substS {F = ℕ} {G = G} {t = n} [Γ]′ [ℕ] [G]′ [n]
        [z]′ = S.irrelevanceTerm {A = G [ zero ]} {t = z} [Γ]₁ [Γ]′
                                 [G₀] [G₀]′ [z]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [G₊] [G₊]′ [s]
    in  [Γ]′ , [Gₙ]′
    ,   natrecᵛ {F = G} {z} {s} {n} [Γ]′ [ℕ] [G]′ [G₀]′ [G₊]′ [Gₙ]′ [z]′ [s]′ [n]
  fundamentalTerm (Emptyrecⱼ {A} {n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , Emptyrecᵛ {F = A} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (starⱼ x) = valid x , Unitᵛ (valid x) , starᵛ {l = ¹} (valid x)
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A)
    with fundamentalTerm ⊢t | fundamentalEq A′≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A) | [Γ] , [A′] , [t]
    | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [Γ]′ = [Γ]₁
          [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A′] [A′]₁ [t]
      in  [Γ]′ , [A]
      ,   convᵛ {t = t} {A} {B} [Γ]′ [A′]₁ [A] [A′≡A] [t]′

  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀ {A t t′} → Γ ⊢ t ≡ t′ ∷ A
                    → ∃ λ ([Γ] : ⊩ᵛ Γ) →
                      [ Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ t′ ∷ A / [Γ] ]
  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] =
    [Γ] , modelsTermEq [A] [t] [t]
                       (λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                              (proj₁ ([t] ⊢Δ [σ])))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t′] [t] [t′≡t] =
    [Γ] , modelsTermEq [A] [t] [t′]
                       (λ ⊢Δ [σ] → symEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                             ([t′≡t] ⊢Δ [σ]))
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t′
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u]
    | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
      let [r]′ = S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁
      in  [Γ] , modelsTermEq [A] [t] [r]′
                  (λ ⊢Δ [σ] →
                     let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                         [t≡u]₁′ = irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ]′))
                                                     (proj₁ ([A] ⊢Δ [σ]))
                                                     ([t≡u]₁ ⊢Δ [σ]′)
                     in  transEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                     ([t≡u] ⊢Δ [σ]) [t≡u]₁′)
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A′≡A)
    with fundamentalTermEq t≡u | fundamentalEq A′≡A
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A′≡A)
    | [Γ] , modelsTermEq [A′] [t] [u] [t≡u] | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A′] [A′]₁ [t]
          [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A′] [A′]₁ [u]
          [t]″ = convᵛ {t = t} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [t]′
          [u]″ = convᵛ {t = u} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [u]′
      in  [Γ]₁
      ,   modelsTermEq [A] [t]″ [u]″
            (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                   [t≡u]′ = irrelevanceEqTerm (proj₁ ([A′] ⊢Δ [σ]′))
                                              (proj₁ ([A′]₁ ⊢Δ [σ]))
                                              ([t≡u] ⊢Δ [σ]′)
               in  convEqTerm₁ (proj₁ ([A′]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
                               ([A′≡A] ⊢Δ [σ]) [t≡u]′)
  fundamentalTermEq (Π-cong {E} {F} {G} {H} ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = Uᵛ [Γ]
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = U} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = univᵛ {A = H} [Γ] [U]′ [H]ₜ′
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {A = F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = Uᵛ (_∙_ {A = F} [Γ] [F])
        [U]₂′ = Uᵛ (_∙_ {A = H} [Γ] [H])
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = U} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ})
                  (S.irrelevanceTerm {A = U} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = U} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] (Uᵛ [Γ]) [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = U} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [U]′
          (Πᵗᵛ {F = F} {G} [Γ] [F] (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [F]ₜ′ [G]ₜ′)
          (Πᵗᵛ {F = H} {E} [Γ] [H] (λ {_} {Δ} {σ} → [U]₂′ {Δ = Δ} {σ}) [H]ₜ′ [E]ₜ′)
          (Π-congᵗᵛ {F = F} {G} {H} {E} [Γ] [F] [H]
                    (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) (λ {_} {Δ} {σ} → [U]₂′ {Δ = Δ} {σ})
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′)
  fundamentalTermEq (Σ-cong {E} {F} {G} {H} ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = Uᵛ [Γ]
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = U} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = univᵛ {A = H} [Γ] [U]′ [H]ₜ′
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {A = F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = Uᵛ (_∙_ {A = F} [Γ] [F])
        [U]₂′ = Uᵛ (_∙_ {A = H} [Γ] [H])
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = U} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ})
                  (S.irrelevanceTerm {A = U} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = U} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] (Uᵛ [Γ]) [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = U} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [U]′
          (Σᵗᵛ {F = F} {G} [Γ] [F] (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) [F]ₜ′ [G]ₜ′)
          (Σᵗᵛ {F = H} {E} [Γ] [H] (λ {_} {Δ} {σ} → [U]₂′ {Δ = Δ} {σ}) [H]ₜ′ [E]ₜ′)
          (Σ-congᵗᵛ {F = F} {G} {H} {E} [Γ] [F] [H]
                    (λ {_} {Δ} {σ} → [U]₁′ {Δ = Δ} {σ}) (λ {_} {Δ} {σ} → [U]₂′ {Δ = Δ} {σ})
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′)
  fundamentalTermEq (∪-cong {A} {B} {C} {D} A≡B C≡D)
    with fundamentalTermEq A≡B | fundamentalTermEq C≡D
  ... | [Γ]₁ , modelsTermEq [U] [A]ₜ [B]ₜ [A≡B]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [C]ₜ [D]ₜ [C≡D]ₜ =
    let [U]₁′   = Uᵛ [Γ]₁
        [A]ₜ′   = S.irrelevanceTerm {A = U} {t = A} [Γ]₁ [Γ]₁ [U] [U]₁′ [A]ₜ
        [B]ₜ′   = S.irrelevanceTerm {A = U} {t = B} [Γ]₁ [Γ]₁ [U] [U]₁′ [B]ₜ
        [C]ₜ′   = S.irrelevanceTerm {A = U} {t = C} [Γ]₂ [Γ]₁ [U]₁ [U]₁′ [C]ₜ
        [D]ₜ′   = S.irrelevanceTerm {A = U} {t = D} [Γ]₂ [Γ]₁ [U]₁ [U]₁′ [D]ₜ
        [A≡B]ₜ′ = S.irrelevanceEqTerm {A = U} {t = A} {u = B} [Γ]₁ [Γ]₁ [U] [U]₁′ [A≡B]ₜ
        [C≡D]ₜ′ = S.irrelevanceEqTerm {A = U} {t = C} {u = D} [Γ]₂ [Γ]₁ [U]₁ [U]₁′ [C≡D]ₜ
    in [Γ]₁ ,
       modelsTermEq [U]₁′
         (∪ᵗᵛ {F = A} {C} [Γ]₁ [A]ₜ′ [C]ₜ′)
         (∪ᵗᵛ {F = B} {D} [Γ]₁ [B]ₜ′ [D]ₜ′)
         (∪-congᵗᵛ {F = A} {C} {B} {D} [Γ]₁ [A]ₜ′ [C]ₜ′ [B]ₜ′ [D]ₜ′ [A≡B]ₜ′ [C≡D]ₜ′)
  fundamentalTermEq (∥-cong {A} {B} A≡B)
    with fundamentalTermEq A≡B
  ... | [Γ]₁ , modelsTermEq [U] [A]ₜ [B]ₜ [A≡B]ₜ =
    let [U]₁′   = Uᵛ [Γ]₁
        [A]ₜ′   = S.irrelevanceTerm {A = U} {t = A} [Γ]₁ [Γ]₁ [U] [U]₁′ [A]ₜ
        [B]ₜ′   = S.irrelevanceTerm {A = U} {t = B} [Γ]₁ [Γ]₁ [U] [U]₁′ [B]ₜ
        [A≡B]ₜ′ = S.irrelevanceEqTerm {A = U} {t = A} {u = B} [Γ]₁ [Γ]₁ [U] [U]₁′ [A≡B]ₜ
    in [Γ]₁ ,
       modelsTermEq [U]₁′
         (∥ᵗᵛ {F = A} [Γ]₁ [A]ₜ′)
         (∥ᵗᵛ {F = B} [Γ]₁ [B]ₜ′)
         (∥-congᵗᵛ {F = A} {B} [Γ]₁ [A]ₜ′ [B]ₜ′ [A≡B]ₜ′)
  fundamentalTermEq (app-cong {a} {b} {f} {g} {F} {G} f≡g a≡b)
    with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g]
      | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]′ = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [f]′ = S.irrelevanceTerm {A = Π F ▹ G} {t = f} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f]
        [g]′ = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [g]
        [f≡g]′ = S.irrelevanceEqTerm {A = Π F ▹ G} {t = f} {u = g}
                                     [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f≡g]
        [G[a]] = substSΠ {F = F} {G} {a} BΠ [Γ]₁ [F] [ΠFG]′ [a]
        [G[b]] = substSΠ {F = F} {G} {b} BΠ [Γ]₁ [F] [ΠFG]′ [b]
        [G[a]≡G[b]] = substSΠEq {F = F} {G} {F} {G} {a} {b} BΠ [Γ]₁ [F] [F] [ΠFG]′
                                [ΠFG]′ (reflᵛ {A = Π F ▹ G} [Γ]₁ [ΠFG]′) [a] [b] [a≡b]
    in  [Γ]₁ , modelsTermEq [G[a]]
                            (appᵛ {F = F} {G} {f} {a} [Γ]₁ [F] [ΠFG]′ [f]′ [a])
                            (conv₂ᵛ {t = g ∘ b} {G [ a ]} {G [ b ]} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appᵛ {F = F} {G} {g} {b}
                                          [Γ]₁ [F] [ΠFG]′ [g]′ [b]))
                            (app-congᵛ {F = F} {G} {f} {g} {a} {b}
                                       [Γ]₁ [F] [ΠFG]′ [f≡g]′ [a] [b] [a≡b])
  fundamentalTermEq (β-red {a} {b} {F} {G} ⊢F ⊢b ⊢a)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]′ = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]′ [b]
        [G[a]] = substS {F = F} {G} {a} [Γ]₂ [F]₁ [G]′ [a]
        [b[a]] = substSTerm {F = F} {G} {a} {b} [Γ]₂ [F]₁ [G]′ [b]′ [a]
        [lam] , [eq] =
          redSubstTermᵛ {A = G [ a ]} {(lam b) ∘ a} {b [ a ]} [Γ]₂
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = escape (proj₁ ([F]₁ ⊢Δ [σ]))
                   ⊢σb = escapeTerm (proj₁ ([G]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = escapeTerm (proj₁ ([F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ (lam (subst (liftSubst σ) b))
                                          ∘ (subst σ a) ⇒ x ∷ y)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red ⊢σF ⊢σb ⊢σa))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (η-eq {f} {g} {F} {G} ⊢F ⊢t ⊢t′ t≡t′) with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t′ | fundamentalTermEq t≡t′
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t′]
      | [Γ]₃ , modelsTermEq [G] [t0] [t′0] [t0≡t′0] =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]′ = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]′) [G]
        [t′]′ = S.irrelevanceTerm {A = Π F ▹ G} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t′]
        [ΠFG]″ = Πᵛ {F = F} {G} [Γ]₁ [F]′ [G]′
        [t]″ = S.irrelevanceTerm {A = Π F ▹ G} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]″ [t]
        [t′]″ = S.irrelevanceTerm {A = Π F ▹ G} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]″ [t′]
        [t0≡t′0]′ = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var x0}
                                        {u = wk1 g ∘ var x0}
                                        [Γ]₃ ([Γ]₁ ∙ [F]′) [G] [G]′ [t0≡t′0]
        [t≡t′] = η-eqᵛ {f = f} {g} {F} {G} [Γ]₁ [F]′ [G]′ [t]″ [t′]″ [t0≡t′0]′
        [t≡t′]′ = S.irrelevanceEqTerm {A = Π F ▹ G} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]″ [ΠFG] [t≡t′]
    in  [Γ]₁ , modelsTermEq [ΠFG] [t] [t′]′ [t≡t′]′
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucᵛ {n = t} [Γ] [A] [t]
          [sucu] = sucᵛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′}
                                 F≡F′ z≡z′ s≡s′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq z≡z′      |
         fundamentalTermEq s≡s′      |
         fundamentalTermEq n≡n′
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′}
                                 F≡F′ z≡z′ s≡s′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z′] [z≡z′] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s′] [s≡s′] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n′] [n≡n′] =
      let sType = Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
          s′Type = Π ℕ ▹ (F′ ▹▹ F′ [ suc (var x0) ]↑)
          [0] = S.irrelevanceTerm {l = ¹} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕᵛ [Γ]₃) [ℕ] (zeroᵛ {l = ¹} [Γ]₃)
          [F]′ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₁ [Γ]₃ [F₀]
          [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]₃ [F₊]
          [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ]₃ [ℕ] [F]′ [n]
          [F′]′ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ [ℕ]) [F′]
          [F₀]″ = substS {F = ℕ} {F} {zero} [Γ]₃ [ℕ] [F]′ [0]
          [F′₀]′ = substS {F = ℕ} {F′} {zero} [Γ]₃ [ℕ] [F′]′ [0]
          [F′₊]′ = sucCase {F = F′} [Γ]₃ [ℕ] [F′]′
          [F′ₙ′]′ = substS {F = ℕ} {F′} {n′} [Γ]₃ [ℕ] [F′]′ [n′]
          [ℕ≡ℕ] = reflᵛ {A = ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflᵗᵛ {A = ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]′ [F≡F′]
          [F₀≡F′₀] = substSEq {F = ℕ} {ℕ} {F} {F′} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]′ [F′]′ [F≡F′]′ [0] [0] [0≡0]
          [F₀≡F′₀]′ = S.irrelevanceEq {A = F [ zero ]} {B = F′ [ zero ]}
                                      [Γ]₃ [Γ]₃ [F₀]″ [F₀]′ [F₀≡F′₀]
          [F₊≡F′₊] = sucCaseCong {F = F} {F′} [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
          [F₊≡F′₊]′ = S.irrelevanceEq {A = sType} {B = s′Type}
                                      [Γ]₃ [Γ]₃ (sucCase {F = F} [Γ]₃ [ℕ] [F]′)
                                      [F₊]′ [F₊≡F′₊]
          [Fₙ≡F′ₙ′]′ = substSEq {F = ℕ} {ℕ} {F} {F′} {n} {n′}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]′ [F′]′ [F≡F′]′
                                [n] [n′] [n≡n′]
          [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z]
          [z′]′ = convᵛ {t = z′} {F [ zero ]} {F′ [ zero ]}
                        [Γ]₃ [F₀]′ [F′₀]′ [F₀≡F′₀]′
                        (S.irrelevanceTerm {A = F [ zero ]} {t = z′}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z′])
          [z≡z′]′ = S.irrelevanceEqTerm {A = F [ zero ]} {t = z} {u = z′}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z≡z′]
          [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s]
          [s′]′ = convᵛ {t = s′} {sType} {s′Type} [Γ]₃ [F₊]′ [F′₊]′ [F₊≡F′₊]′
                        (S.irrelevanceTerm {A = sType} {t = s′}
                                           [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s′])
          [s≡s′]′ = S.irrelevanceEqTerm {A = sType} {t = s} {u = s′}
                                        [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s≡s′]
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]′
                       (natrecᵛ {F = F} {z} {s} {n}
                                [Γ]₃ [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n])
                       (conv₂ᵛ {t = natrec F′ z′ s′ n′} {F [ n ]} {F′ [ n′ ]}
                               [Γ]₃ [Fₙ]′ [F′ₙ′]′ [Fₙ≡F′ₙ′]′
                               (natrecᵛ {F = F′} {z′} {s′} {n′}
                                        [Γ]₃ [ℕ] [F′]′ [F′₀]′ [F′₊]′ [F′ₙ′]′
                                        [z′]′ [s′]′ [n′]))
                       (natrec-congᵛ {F = F} {F′} {z} {z′} {s} {s′} {n} {n′}
                                     [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
                                     [F₀]′ [F′₀]′ [F₀≡F′₀]′
                                     [F₊]′ [F′₊]′ [F₊≡F′₊]′ [Fₙ]′
                                     [z]′ [z′]′ [z≡z′]′
                                     [s]′ [s′]′ [s≡s′]′ [n] [n′] [n≡n′])
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s) | [Γ] , [F]
    | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
        [Γ]′ = [Γ]₁
        [ℕ]′ = ℕᵛ {l = ¹} [Γ]′
        [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [F₊]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [F₊] [F₊]′ [s]
        [F]′ = S.irrelevance {A = F} [Γ] ([Γ]′ ∙ [ℕ]′) [F]
        d , r =
          redSubstTermᵛ {A = F [ zero ]} {natrec F z s zero} {z} [Γ]′
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]′ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x)
                                 (natrecSucCase σ F)
                                 (escapeTerm (proj₁ ([F₊]′ ⊢Δ [σ]))
                                                (proj₁ ([s]′ ⊢Δ [σ])))
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s zero)
                                    ⇒ subst σ z ∷ x)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]′ , modelsTermEq [F₀] d [z] r
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]′ = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]′ = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]′ [n]
        [sucn] = sucᵛ {n = n} [Γ]₃ [ℕ]′ [n]′
        [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₂ [Γ]₃ [F₀]
        [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                 [Γ]₂ [Γ]₃ [F₀] [F₀]′ [z]
        [F]′ = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]′) [F]
        [F[sucn]] = substS {F = ℕ} {F} {suc n} [Γ]₃ [ℕ]′ [F]′ [sucn]
        [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ]₃ [ℕ]′ [F]′ [n]′
        [natrecₙ] = natrecᵛ {F = F} {z} {s} {n}
                            [Γ]₃ [ℕ]′ [F]′ [F₀]′ [F₊] [Fₙ]′ [z]′ [s] [n]′
        t = (s ∘ n) ∘ (natrec F z s n)
        q = subst (liftSubst (sgSubst n))
                  (wk1 (F [ suc (var x0) ]↑))
        y = S.irrelevanceTerm′
              {A = q [ natrec F z s n ]} {A′ = F [ suc n ]} {t = t}
              (natrecIrrelevantSubst′ F z s n) [Γ]₃ [Γ]₃
              (substSΠ {F = F [ n ]} {q} {natrec F z s n} BΠ [Γ]₃
                (substS {F = ℕ} {F} {n} [Γ]₃ [ℕ]′ [F]′ [n]′)
                (substSΠ {F = ℕ} {F ▹▹ F [ suc (var x0) ]↑} {n}
                         BΠ [Γ]₃ [ℕ]′ [F₊] [n]′)
                [natrecₙ])
              [F[sucn]]
              (appᵛ {F = F [ n ]} {q} {s ∘ n} {natrec F z s n} [Γ]₃ [Fₙ]′
                (substSΠ {F = ℕ} {F ▹▹ F [ suc (var x0) ]↑} {n}
                         BΠ [Γ]₃ [ℕ]′ [F₊] [n]′)
                (appᵛ {F = ℕ} {F ▹▹ F [ suc (var x0) ]↑} {s} {n}
                      [Γ]₃ [ℕ]′ [F₊] [s] [n]′)
                [natrecₙ])
        d , r =
          redSubstTermᵛ {A = F [ suc n ]} {natrec F z s (suc n)} {t } {¹} [Γ]₃
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let ⊢n = escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ]))
                                      (proj₁ ([n]′ ⊢Δ [σ]))
                   ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]₃ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀]′ ⊢Δ [σ]))
                                                (proj₁ ([z]′ ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x)
                                 (natrecSucCase σ F)
                                 (escapeTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                (proj₁ ([s] ⊢Δ [σ])))
                   r = _⊢_⇒_∷_.natrec-suc {_} {n = subst σ n}
                                          {z = subst σ z} {s = subst σ s}
                                          {F = subst (liftSubst σ) F}
                                          ⊢n ⊢F ⊢z ⊢s
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s (suc n))
                                    ⇒ (subst σ t) ∷ x)
                           (PE.trans (PE.trans (substCompEq F)
                             (substVar-to-subst (λ { x0 → PE.refl
                                         ; (x +1) → PE.trans (subst-wk (σ x))
                                                              (subst-id (σ x))
                                         })
                                      F))
                             (PE.sym (substCompEq F)))
                           r)
                        [F[sucn]] y
    in  [Γ]₃ , modelsTermEq [F[sucn]] d y r
  fundamentalTermEq (Emptyrec-cong {F} {F′} {n} {n′}
                                 F≡F′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq n≡n′
  fundamentalTermEq (Emptyrec-cong {F} {F′} {n} {n′}
                                 F≡F′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]′ , modelsTermEq [Empty] [n] [n′] [n≡n′] =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]′ [F]
        [F′]′ = S.irrelevance {A = F′} [Γ] [Γ]′ [F′]
        [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} [Γ] [Γ]′ [F] [F]′ [F≡F′]
    in [Γ]′
      , modelsTermEq [F]′ (Emptyrecᵛ {F = F} {n} [Γ]′ [Empty] [F]′ [n])
                     (conv₂ᵛ {t = Emptyrec F′ n′} {F} {F′} [Γ]′ [F]′ [F′]′ [F≡F′]′
                       (Emptyrecᵛ {F = F′} {n′} [Γ]′ [Empty] [F′]′ [n′]))
                     (Emptyrec-congᵛ {F = F} {F′} {n} {n′}
                       [Γ]′ [Empty] [F]′ [F′]′ [F≡F′]′
                       [n] [n′] [n≡n′])
  fundamentalTermEq (η-unit {e} {e'} ⊢e ⊢e')
    with fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , [Unit] , [e] | [Γ]' , [Unit]' , [e'] =
    let [e'] = S.irrelevanceTerm {A = Unit} {t = e'} [Γ]' [Γ] [Unit]' [Unit] [e']
    in  [Γ] , modelsTermEq [Unit] [e] [e'] (η-unitᵛ {e = e} {e' = e'} [Γ] [Unit] [e] [e'])
  fundamentalTermEq (fst-cong {t} {t′} {F} {G} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]′ = S.irrelevanceTerm {A = Σ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                 [t]
        [t′]′ = S.irrelevanceTerm {A = Σ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                  [t′]
        [t≡t′]′ = S.irrelevanceEqTerm {A = Σ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                                      [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                      [t≡t′]

        [fstt] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]′
        [fstt′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]′
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]′ [t′]′ [t≡t′]′
    in  [Γ] , modelsTermEq [F] [fstt] [fstt′] [fst≡]
  fundamentalTermEq {Γ = Γ} (snd-cong {t} {t′} {F} {G} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]Σ = S.irrelevanceTerm {A = Σ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                 [t]
        [t′]Σ = S.irrelevanceTerm {A = Σ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                  [t′]
        [t≡t′]Σ = S.irrelevanceEqTerm {A = Σ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                                      [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                      [t≡t′]

        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]Σ
        [fst′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]Σ
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]Σ [t′]Σ [t≡t′]Σ
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [Gfst′] = substS {F = F} {G} [Γ] [F] [G] [fst′]
        [Gfst≡] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = fst t} {t′ = fst t′} [Γ]
                           [F] [F] (reflᵛ {A = F} [Γ] [F])
                           [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                           [fst] [fst′] [fst≡]
        [snd] = sndᵛ {F = F} {G} {t} [Γ] [F] [G] [t]Σ
        [snd′]fst′ = sndᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]Σ
        [snd′]fst = conv₂ᵛ {t = snd t′} {A = G [ fst t ]} {B = G [ fst t′ ]}
                           [Γ] [Gfst] [Gfst′] [Gfst≡] [snd′]fst′
        [snd≡] = snd-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]Σ [t′]Σ [t≡t′]Σ
    in  [Γ] , modelsTermEq [Gfst] [snd] [snd′]fst [snd≡]
  fundamentalTermEq (Σ-β₁ {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [u] = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ (substS {F = F} {G} [Γ] [F] [G] [t])
                                [u]₂

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
        [fst] = fstᵛ {F = F} {G} {prod t u} [Γ] [F] [G] [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
    in  [Γ] , modelsTermEq [F] [fst] [t] [fst≡t]
  fundamentalTermEq {Γ = Γ} (Σ-β₂ {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
        [u] = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ [Gt]
                                [u]₂

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
        [fst] = fstᵛ {F = F} {G} {prod t u} [Γ] [F] [G] [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]

        [Gfst≡Gt] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = fst (prod t u)} {t′ = t} [Γ]
                             [F] [F] (reflᵛ {A = F} [Γ] [F])
                             [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                             [fst] [t] [fst≡t]

        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} {prod t u} [Γ] [F] [G] [prod]
        [snd≡u] = Σ-β₂ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]

        [u]fst = conv₂ᵛ {t = u} {A = G [ fst (prod t u) ]} {B = G [ t ]}
                        [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]
    in  [Γ] , modelsTermEq [Gfst] [snd] [u]fst [snd≡u]
  fundamentalTermEq (Σ-η {p = p} {r} {F} {G} ⊢F ⊢G ⊢p ⊢r fst≡ snd≡)
    with fundamentalTerm ⊢p | fundamentalTerm ⊢r |
         fundamental ⊢F | fundamental ⊢G |
         fundamentalTermEq fst≡ | fundamentalTermEq snd≡
  ... | [Γ] , [ΣFG]₀ , [p]₀ | [Γ]₁ , [ΣFG]₁ , [r]₁
      | [Γ]₂ , [F]₂ | [Γ]₃ , [G]₃
      | [Γ]₄ , modelsTermEq [F]₄ [fstp]₄ [fstr]₄ [fst≡]₄
      | [Γ]₅ , modelsTermEq [Gfstp]₅ [sndp]₅ [sndr]₅ [snd≡]₅ =
    let [F] = S.irrelevance {A = F} [Γ]₂ [Γ] [F]₂
        [G] = S.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]₃
        [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
        [p] = S.irrelevanceTerm {A = Σ F ▹ G} {t = p} [Γ] [Γ]
                                [ΣFG]₀ [ΣFG]
                                [p]₀
        [r] = S.irrelevanceTerm {A = Σ F ▹ G} {t = r} [Γ]₁ [Γ]
                                [ΣFG]₁ [ΣFG]
                                [r]₁

        [fst≡] = S.irrelevanceEqTerm {A = F} {t = fst p} {u = fst r} [Γ]₄ [Γ]
                                     [F]₄ [F]
                                     [fst≡]₄

        [Gfstp] = substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {p} [Γ] [F] [G] [p])
        [snd≡] = S.irrelevanceEqTerm {A = G [ fst p ]} {t = snd p} {u = snd r} [Γ]₅ [Γ]
                                     [Gfstp]₅ [Gfstp]
                                     [snd≡]₅

        [p≡r] = Σ-ηᵛ {F = F} {G} {p} {r}
                     [Γ] [F] [G] [p] [r] [fst≡] [snd≡]
    in  [Γ] , modelsTermEq [ΣFG] [p] [r] [p≡r]
  fundamentalTermEq (injl-cong {t} {t′} {A} {B} ⊢B t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢B
  ... | [Γ] , modelsTermEq [A] [t] [t′] [t≡t′]
      | [Γ]₂ , [B]₂ =
    let [B] = S.irrelevance {A = B} [Γ]₂ [Γ] [B]₂
        [∪AB] = ∪ᵛ {F = A} {B} [Γ] [A] [B]
    in  [Γ] , modelsTermEq [∪AB]
                (injlᵛ {A = A} {B} {t} [Γ] [A] [B] [t])
                (injlᵛ {A = A} {B} {t′} [Γ] [A] [B] [t′])
                (injl-congᵛ {A = A} {B} {t} {t′} [Γ] [A] [B] [t] [t′] [t≡t′])
  fundamentalTermEq (injr-cong {t} {t′} {A} {B} ⊢A t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢A
  ... | [Γ] , modelsTermEq [B] [t] [t′] [t≡t′]
      | [Γ]₁ , [A]₁ =
    let [A] = S.irrelevance {A = A} [Γ]₁ [Γ] [A]₁
        [∪AB] = ∪ᵛ {F = A} {B} [Γ] [A] [B]
    in  [Γ] , modelsTermEq [∪AB]
                (injrᵛ {A = A} {B} {t} [Γ] [A] [B] [t])
                (injrᵛ {A = A} {B} {t′} [Γ] [A] [B] [t′])
                (injr-congᵛ {A = A} {B} {t} {t′} [Γ] [A] [B] [t] [t′] [t≡t′])
  fundamentalTermEq (cases-cong {t} {t′} {u} {u′} {v} {v′} {A} {B} {C} {C′} ⊢A ⊢B ⊢C≡C′ t≡t′ u≡u′ v≡v′)
    with fundamental ⊢A
       | fundamental ⊢B
       | fundamentalEq ⊢C≡C′
       | fundamentalTermEq t≡t′
       | fundamentalTermEq u≡u′
       | fundamentalTermEq v≡v′
  ... | [Γ]₁ , [A]₁ | [Γ]₂ , [B]₂ | [Γ]₃ , [C]₃ , [C′]₃ , [C≡C′]₃
      | [Γ]₄ , modelsTermEq [A∪B]₄ [t]₄ [t′]₄ [t≡t′]₄
      | [Γ]₅ , modelsTermEq [A▹▹C]₅ [u]₅ [u′]₅ [u≡u′]₅
      | [Γ]₆ , modelsTermEq [B▹▹C]₆ [v]₆ [v′]₆ [v≡v′]₆ =
    let [Γ]    = [Γ]₁
        [A]    = S.irrelevance {A = A} [Γ]₁ [Γ] [A]₁
        [B]    = S.irrelevance {A = B} [Γ]₂ [Γ] [B]₂
        [C]    = S.irrelevance {A = C} [Γ]₃ [Γ] [C]₃
        [C′]   = S.irrelevance {A = C′} [Γ]₃ [Γ] [C′]₃
        [t]    = S.irrelevanceTerm {A = A ∪ B} {t = t} [Γ]₄ [Γ] [A∪B]₄ (∪ᵛ {F = A} {B} [Γ] [A] [B]) [t]₄
        [u]    = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₅ [Γ] [A▹▹C]₅ (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) [u]₅
        [v]    = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₆ [Γ] [B▹▹C]₆ (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) [v]₆
        [t′]   = S.irrelevanceTerm {A = A ∪ B} {t = t′} [Γ]₄ [Γ] [A∪B]₄ (∪ᵛ {F = A} {B} [Γ] [A] [B]) [t′]₄
        [u′]   = S.irrelevanceTerm {A = A ▹▹ C} {t = u′} [Γ]₅ [Γ] [A▹▹C]₅ (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) [u′]₅
        [v′]   = S.irrelevanceTerm {A = B ▹▹ C} {t = v′} [Γ]₆ [Γ] [B▹▹C]₆ (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) [v′]₆
        [C≡C′] = S.irrelevanceEq {A = C} {B = C′} [Γ]₃ [Γ] [C]₃ [C] [C≡C′]₃
        [t≡t′] = S.irrelevanceEqTerm {A = A ∪ B} {t = t} {u = t′}  [Γ]₄ [Γ] [A∪B]₄ (∪ᵛ {F = A} {B} [Γ] [A] [B]) [t≡t′]₄
        [u≡u′] = S.irrelevanceEqTerm {A = A ▹▹ C} {t = u} {u = u′} [Γ]₅ [Γ] [A▹▹C]₅ (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) [u≡u′]₅
        [v≡v′] = S.irrelevanceEqTerm {A = B ▹▹ C} {t = v} {u = v′} [Γ]₆ [Γ] [B▹▹C]₆ (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) [v≡v′]₆
    in [Γ] ,
       modelsTermEq [C]
                    (casesᵛ {A = A} {B} {C} {t = t} {u = u} {v = v} [Γ] [A] [B] [C] [t] [u] [v])
                    (S.irrelevanceTerm″ {A = C′} {A′ = C} {t = cases C′ t′ u′ v′}
                      [Γ] [Γ] [C′] [C] (⊩ᵛ-sym {A = C} {B = C′} [Γ] [C] [C′] [C≡C′])
                      (casesᵛ {A = A} {B} {C′} {t = t′} {u = u′} {v = v′} [Γ] [A] [B] [C′] [t′]
                        (S.irrelevanceTerm″ {A = A ▹▹ C} {A′ = A ▹▹ C′} {t = u′}
                          [Γ] [Γ] (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) (▹▹ᵛ {F = A} {C′} [Γ] [A] [C′])
                          (▹▹-congᵛ′ {A = A} {C = C} {C′ = C′} [Γ] [A] [C] [C′] [C≡C′])
                          [u′])
                        (S.irrelevanceTerm″ {A = B ▹▹ C} {A′ = B ▹▹ C′} {t = v′} [Γ] [Γ]
                          (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) (▹▹ᵛ {F = B} {C′} [Γ] [B] [C′])
                          (▹▹-congᵛ′ {A = B} {C = C} {C′ = C′} [Γ] [B] [C] [C′] [C≡C′])
                          [v′])))
                    (cases-congᵛ
                      {A = A} {B} {C} {C′} {t = t} {t′ = t′} {u = u} {u′ = u′} {v = v} {v′ = v′} [Γ] [A] [B]
                      [C] [C′] [C≡C′]
                      [t≡t′] [u≡u′] [v≡v′])
  fundamentalTermEq (∪-β₁ {A} {B} {C} {t} {u} {v} ⊢B ⊢C ⊢t ⊢u ⊢v)
    with fundamental ⊢B
       | fundamental ⊢C
       | fundamentalTerm ⊢t
       | fundamentalTerm ⊢u
       | fundamentalTerm ⊢v
  ... | [Γ]₂ , [B]₂ | [Γ]₃ , [C]₃
      | [Γ]₄ , [A]₄ , [t]₄
      | [Γ]₅ , [A▹▹C]₅ , [u]₅
      | [Γ]₆ , [B▹▹C]₆ , [v]₆ =
    let [Γ]    = [Γ]₂
        [A]    = S.irrelevance {A = A} [Γ]₄ [Γ] [A]₄
        [B]    = S.irrelevance {A = B} [Γ]₂ [Γ] [B]₂
        [C]    = S.irrelevance {A = C} [Γ]₃ [Γ] [C]₃
        [A▹▹C] = S.irrelevance {A = A ▹▹ C} [Γ]₅ [Γ] [A▹▹C]₅
        [B▹▹C] = S.irrelevance {A = B ▹▹ C} [Γ]₆ [Γ] [B▹▹C]₆
        [t]    = S.irrelevanceTerm {A = A} {t = t} [Γ]₄ [Γ] [A]₄ [A] [t]₄
        [u]    = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₅ [Γ] [A▹▹C]₅ (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) [u]₅
        [v]    = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₆ [Γ] [B▹▹C]₆ (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) [v]₆
        [u]′   = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₅ [Γ] [A▹▹C]₅ [A▹▹C] [u]₅
        [v]′   = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₆ [Γ] [B▹▹C]₆ [B▹▹C] [v]₆
    in [Γ] ,
       modelsTermEq [C]
                    (casesᵛ {A = A} {B} {C} {t = injl t} {u = u} {v = v} [Γ] [A] [B] [C]
                            (injlᵛ {A = A} {B = B} {t = t} [Γ] [A] [B] [t]) [u] [v])
                    (▹▹appᵛ {F = A} {G = C} {t = u} {u = t} [Γ] [A] [C] [A▹▹C] [u]′ [t])
                    (cases-βₗᵛ {A = A} {B} {C} {t = t} {u = u} {v = v} [Γ] [C] [A] [B] [t] [u] [v])
  fundamentalTermEq (∪-β₂ {A} {B} {C} {t} {u} {v} ⊢A ⊢C ⊢t ⊢u ⊢v)
    with fundamental ⊢A
       | fundamental ⊢C
       | fundamentalTerm ⊢t
       | fundamentalTerm ⊢u
       | fundamentalTerm ⊢v
  ... | [Γ]₁ , [A]₁
      | [Γ]₃ , [C]₃
      | [Γ]₄ , [B]₄ , [t]₄
      | [Γ]₅ , [A▹▹C]₅ , [u]₅
      | [Γ]₆ , [B▹▹C]₆ , [v]₆ =
    let [Γ]    = [Γ]₁
        [A]    = S.irrelevance {A = A} [Γ]₁ [Γ] [A]₁
        [B]    = S.irrelevance {A = B} [Γ]₄ [Γ] [B]₄
        [C]    = S.irrelevance {A = C} [Γ]₃ [Γ] [C]₃
        [A▹▹C] = S.irrelevance {A = A ▹▹ C} [Γ]₅ [Γ] [A▹▹C]₅
        [B▹▹C] = S.irrelevance {A = B ▹▹ C} [Γ]₆ [Γ] [B▹▹C]₆
        [t]    = S.irrelevanceTerm {A = B} {t = t} [Γ]₄ [Γ] [B]₄ [B] [t]₄
        [u]    = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₅ [Γ] [A▹▹C]₅ (▹▹ᵛ {F = A} {C} [Γ] [A] [C]) [u]₅
        [v]    = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₆ [Γ] [B▹▹C]₆ (▹▹ᵛ {F = B} {C} [Γ] [B] [C]) [v]₆
        [u]′   = S.irrelevanceTerm {A = A ▹▹ C} {t = u} [Γ]₅ [Γ] [A▹▹C]₅ [A▹▹C] [u]₅
        [v]′   = S.irrelevanceTerm {A = B ▹▹ C} {t = v} [Γ]₆ [Γ] [B▹▹C]₆ [B▹▹C] [v]₆
    in [Γ] ,
       modelsTermEq [C]
                    (casesᵛ {A = A} {B} {C} {t = injr t} {u = u} {v = v} [Γ] [A] [B] [C]
                            (injrᵛ {A = A} {B = B} {t = t} [Γ] [A] [B] [t]) [u] [v])
                    (▹▹appᵛ {F = B} {G = C} {t = v} {u = t} [Γ] [B] [C] [B▹▹C] [v]′ [t])
                    (cases-βᵣᵛ {A = A} {B} {C} {t = t} {u = u} {v = v} [Γ] [C] [A] [B] [t] [u] [v])
  fundamentalTermEq (∥ᵢ-cong {t} {t′} {A} ⊢A t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢A
  ... | [Γ] , modelsTermEq [A] [t] [t′] [t≡t′] | [Γ]₁ , [A]₁ =
    let [∥A∥] = ∥ᵛ {F = A} [Γ] [A]
    in  [Γ] , modelsTermEq [∥A∥]
                (∥ᵢᵛ {A = A} {t}  [Γ] [A] [t])
                (∥ᵢᵛ {A = A} {t′} [Γ] [A] [t′])
                (∥ᵢ-congᵛ {A = A} {t} {t′} [Γ] [A] [t] [t′] [t≡t′])
  fundamentalTermEq {Γ = Γ} (∥ₑ-cong {a} {a′} {f} {f′} {A} {B} {B′} ⊢A B≡B′ a≡a′ f≡f′)
    with fundamental ⊢A
       | fundamentalEq B≡B′
       | fundamentalTermEq a≡a′
       | fundamentalTermEq f≡f′
  ... | [Γ]₁ , [A]₁ | [Γ]₂ , [B]₂ , [B′]₂ , [B≡B′]₂
      | [Γ]₃ , modelsTermEq [∥A∥]₃ [a]₃ [a′]₃ [a≡a′]₃
      | [Γ]₄ , modelsTermEq [A▹▹B]₄ [f]₄ [f′]₄ [f≡f′]₄ =
    let [Γ]    = [Γ]₁
        [A]    = S.irrelevance {A = A} [Γ]₁ [Γ] [A]₁
        [B]    = S.irrelevance {A = B} [Γ]₂ [Γ] [B]₂
        [∥B∥]  = ⊩ᵛ∥ {Γ = Γ} {A = B} [Γ] [B]
        [B′]   = S.irrelevance {A = B′} [Γ]₂ [Γ] [B′]₂
        [∥B′∥] = ⊩ᵛ∥ {Γ = Γ} {A = B′} [Γ] [B′]
        [a]    = S.irrelevanceTerm {A = ∥ A ∥} {t = a} [Γ]₃ [Γ] [∥A∥]₃ (∥ᵛ {F = A} [Γ] [A]) [a]₃
        [f]    = S.irrelevanceTerm {A = A ▹▹ ∥ B ∥} {t = f} [Γ]₄ [Γ] [A▹▹B]₄ (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]) [f]₄
        [a′]   = S.irrelevanceTerm {A = ∥ A ∥} {t = a′} [Γ]₃ [Γ] [∥A∥]₃ (∥ᵛ {F = A} [Γ] [A]) [a′]₃
        [f′]   = S.irrelevanceTerm {A = A ▹▹ ∥ B ∥} {t = f′} [Γ]₄ [Γ] [A▹▹B]₄ (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]) [f′]₄
        [B≡B′] = S.irrelevanceEq {A = B} {B = B′} [Γ]₂ [Γ] [B]₂ [B] [B≡B′]₂
        [a≡a′] = S.irrelevanceEqTerm {A = ∥ A ∥} {t = a} {u = a′}  [Γ]₃ [Γ] [∥A∥]₃ (∥ᵛ {F = A} [Γ] [A]) [a≡a′]₃
        [f≡f′] = S.irrelevanceEqTerm {A = A ▹▹ ∥ B ∥} {t = f} {u = f′} [Γ]₄ [Γ] [A▹▹B]₄ (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]) [f≡f′]₄
    in [Γ] ,
       modelsTermEq [∥B∥]
         (∥ₑᵛ {A = A} {B} {a = a} {f = f} [Γ] [A] [B] [∥B∥] [a] [f])
         (S.irrelevanceTerm″
           {A = ∥ B′ ∥} {A′ = ∥ B ∥} {t = ∥ₑ B′ a′ f′} [Γ] [Γ] [∥B′∥] [∥B∥]
           (⊩ᵛ-sym {A = ∥ B ∥} {B = ∥ B′ ∥} [Γ] [∥B∥] [∥B′∥] (⊩≡ᵛ∥ {Γ = Γ} {A = B} {B = B′} [Γ] [B] [B′] [∥B∥] [B≡B′]))
           (∥ₑᵛ {A = A} {B′} {a = a′} {f = f′} [Γ] [A] [B′] [∥B′∥] [a′]
                (S.irrelevanceTerm″ {A = A ▹▹ ∥ B ∥} {A′ = A ▹▹ ∥ B′ ∥} {t = f′} [Γ] [Γ]
                  (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥])
                  (▹▹ᵛ {F = A} {∥ B′ ∥} [Γ] [A] [∥B′∥])
                  (▹▹-congᵛ′ {A = A} {C = ∥ B ∥} {C′ = ∥ B′ ∥} [Γ] [A] [∥B∥] [∥B′∥]
                             (⊩≡ᵛ∥ {Γ = Γ} {A = B} {B = B′} [Γ] [B] [B′] [∥B∥] [B≡B′]))
                  [f′])))
         (∥ₑ-congᵛ {A = A} {B} {B′} {a = a} {a′ = a′} {f = f} {f′ = f′} [Γ] [A] [B] [∥B∥]
                   [B′] [B≡B′] [a≡a′] [f≡f′])
  fundamentalTermEq {Γ = Γ} (∥-β {A} {B} {a} {f} ⊢B ⊢a ⊢f)
    with fundamental ⊢B
       | fundamentalTerm ⊢a
       | fundamentalTerm ⊢f
  ... | [Γ]₂ , [B]₂
      | [Γ]₃ , [A]₃ , [a]₃
      | [Γ]₄ , [A▹▹B]₄ , [f]₄ =
    let [Γ]    = [Γ]₂
        [A]    = S.irrelevance {A = A} [Γ]₃ [Γ] [A]₃
        [B]    = S.irrelevance {A = B} [Γ]₂ [Γ] [B]₂
        [∥B∥]  = ⊩ᵛ∥ {Γ = Γ} {A = B} [Γ] [B]
        [A▹▹B] = S.irrelevance {A = A ▹▹ ∥ B ∥} [Γ]₄ [Γ] [A▹▹B]₄
        [a]    = S.irrelevanceTerm {A = A} {t = a} [Γ]₃ [Γ] [A]₃ [A] [a]₃
        [f]    = S.irrelevanceTerm {A = A ▹▹ ∥ B ∥} {t = f} [Γ]₄ [Γ] [A▹▹B]₄ (▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]) [f]₄
        [f]′   = S.irrelevanceTerm {A = A ▹▹ ∥ B ∥} {t = f} [Γ]₄ [Γ] [A▹▹B]₄ [A▹▹B] [f]₄
    in [Γ] ,
       modelsTermEq [∥B∥]
         (∥ₑᵛ {A = A} {B} {a = ∥ᵢ a} {f = f} [Γ] [A] [B] [∥B∥]
              (∥ᵢᵛ {A = A} {t = a} [Γ] [A] [a]) [f])
         (▹▹appᵛ {F = A} {G = ∥ B ∥} {t = f} {u = a} [Γ] [A] [∥B∥] [A▹▹B] [f]′ [a])
         (∥ₑ-βᵛ {A = A} {B} {a = a} {f = f} [Γ] [A] [B] [∥B∥] [a] [f])

-- Fundamental theorem for substitutions.
fundamentalSubst : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ∷ Γ
      → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , tt
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
      [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]′
  ,   irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])

-- Fundamental theorem for substitution equality.
fundamentalSubstEq : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
      → ∃₂ λ [Γ] [σ]
      → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
fundamentalSubstEq ε ⊢Δ σ = ε , tt , tt , tt
fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
  let [Γ] , [A] = fundamental ⊢A
      [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
      [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
      [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
      [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idA]″ = proj₁ ([A] ⊢Δ [tailσ′]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
      [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
      [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
  in  [Γ] ∙ [A]
  ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])
  ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
                             (proj₂ ([A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
                             (irrelevanceTerm″ (subst-id _) (subst-id _)
                                                [idA] [idA]′ [idt′]))
  ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                                         [idA] [idA]′ [idt≡t′])
