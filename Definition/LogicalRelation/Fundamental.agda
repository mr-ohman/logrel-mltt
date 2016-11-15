module Definition.LogicalRelation.Fundamental where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat.Base renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊩ₛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


-- Fundamental theorem for types

  fundamental : ∀ {Γ A} (⊢A : Γ ⊢ A) → Σ (⊩ₛ Γ) (λ [Γ] → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕ x) = valid x , ℕₛ (valid x)
  fundamental (U x) = valid x , Uₛ (valid x)
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢F | fundamental ⊢G
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , Πₛ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , univₛ {A} [Γ] [U] [A]

-- Fundamental theorem for type equality

  fundamentalEq : ∀{Γ A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ₛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = univₛ {A} [Γ] [U] [t]
        [B] = univₛ {B} [Γ] [U] [u]
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
               let [σ]' = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                           (proj₁ ([B] ⊢Δ [σ]')) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ]'))
                                          (proj₁ ([B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]')))
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [Γ] , [F] , [H] , [F≡H]
    | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]' = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]' = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]' = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]' [G≡E]
      in  [Γ]
      ,   Πₛ {F} {G} [Γ] [F] [G]'
      ,   Πₛ {H} {E} [Γ] [H] [E]'
      ,   Π-congₛ {F} {G} {H} {E} [Γ] [F] [G]' [H] [E]' [F≡H] [G≡E]'

  fundamentalVar : ∀ {Γ A x}
                 → x ∷ A ∈ Γ
                 → ([Γ] : ⊩ₛ Γ)
                 → ∃ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
                 → Γ ⊩ₛ⟨ ¹ ⟩t var x ∷ A / [Γ] / [A]
  fundamentalVar here (_∙_ {A = A} {l = l} [Γ] [A]) =
    (λ ⊢Δ [σ] →
       let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
           [σA'] = maybeEmb (irrelevance' (PE.sym (subst-wk A)) [σA])
       in  [σA']
       ,   (λ [σ'] [σ≡σ'] →
              irrelevanceEq'' (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA'] (proj₂ ([A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ']) (proj₁ [σ≡σ']))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
             [σA'] = maybeEmb (irrelevance' (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm' (PE.sym (subst-wk A)) [σA] [σA'] (proj₂ [σ])
    , (λ [σ'] [σ≡σ'] → irrelevanceEqTerm' (PE.sym (subst-wk A))
                                          [σA] [σA'] (proj₂ [σ≡σ'])))
  fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (λ ⊢Δ [σ] →
       let [h]   = proj₁ (fundamentalVar h [Γ]) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA'] = irrelevance' (PE.sym (subst-wk A)) [σA]
       in  [σA']
       ,   (λ [σ'] [σ≡σ'] →
              irrelevanceEq'' (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA']
                              (proj₂ [h] (proj₁ [σ']) (proj₁ [σ≡σ']))))
    , (λ ⊢Δ [σ] →
         let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA'] = irrelevance' (PE.sym (subst-wk A)) [σA]
             [h'] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         in  irrelevanceTerm' (PE.sym (subst-wk A)) [σA] [σA'] (proj₁ [h'])
         ,   (λ [σ'] [σ≡σ'] →
                irrelevanceEqTerm' (PE.sym (subst-wk A)) [σA] [σA']
                                   (proj₂ [h'] (proj₁ [σ']) (proj₁ [σ≡σ']))))

-- Fundamental theorem for terms

  fundamentalTerm : ∀{Γ A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ₛ Γ)
    → ∃ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕ x) = valid x , Uₛ (valid x) , ℕₜₛ (valid x)
  fundamentalTerm (Π_▹_ {F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univₛ {F} [Γ] [U] [F]ₜ
        [U]'  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ' = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uₛ [Γ]) [F]ₜ
        [G]ₜ' = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁
                                  (λ {Δ} {σ} → [U]' {Δ} {σ}) [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Π F ▹ G} [Γ] [Γ] (Uₛ [Γ]) [U]
                          (Πₜₛ {F} {G} [Γ] [F] (λ {Δ} {σ} → [U]' {Δ} {σ})
                               [F]ₜ' [G]ₜ')
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lam {F} {G} {t} ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]' = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]' = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]' [t]
    in  [Γ] , Πₛ {F} {G} [Γ] [F] [G]'
    ,   lamₛ {F} {G} {t} [Γ] [F] [G]' [t]'
  fundamentalTerm (_∘_ {g} {a} {F} {G} Dt Du)
    with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]' = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [t]' = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]' [t]
        [G[t]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]' [u]
        [t∘u] = appₛ {F} {G} {g} {a} [Γ]₁ [F] [ΠFG]' [t]' [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (zero x) = valid x , ℕₛ (valid x) , zeroₛ (valid x)
  fundamentalTerm (suc {n} t) with fundamentalTerm t
  fundamentalTerm (suc {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucₛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrec {G} {s} {z} {n} ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let sType = Π ℕ ▹ (G ▹▹ G [ suc (var zero) ]↑)
        [Γ]' = [Γ]₃
        [G]' = S.irrelevance {A = G} [Γ] ([Γ]' ∙ [ℕ]) [G]
        [G₀]' = S.irrelevance {A = G [ zero ]} [Γ]₁ [Γ]' [G₀]
        [G₊]' = S.irrelevance {A = sType} [Γ]₂ [Γ]' [G₊]
        [Gₙ]' = substS {F = ℕ} {G = G} {t = n} [Γ]' [ℕ] [G]' [n]
        [z]' = S.irrelevanceTerm {A = G [ zero ]} {t = z} [Γ]₁ [Γ]'
                                 [G₀] [G₀]' [z]
        [s]' = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]' [G₊] [G₊]' [s]
    in  [Γ]' , [Gₙ]'
    ,   natrecₛ {G} {z} {s} {n} [Γ]' [ℕ] [G]' [G₀]' [G₊]' [Gₙ]' [z]' [s]' [n]
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A)
    with fundamentalTerm ⊢t | fundamentalEq A'≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A) | [Γ] , [A'] , [t]
    | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
      let [Γ]' = [Γ]₁
          [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]' [A'] [A']₁ [t]
      in  [Γ]' , [A]
      ,   convₛ {t} {A} {B} [Γ]' [A']₁ [A] [A'≡A] [t]'

-- Fundamental theorem for term equality

  fundamentalTermEq : ∀{Γ A t t'} → Γ ⊢ t ≡ t' ∷ A
                    → ∃ λ ([Γ] : ⊩ₛ Γ)
                    → Γ ⊩ₛ⟨ ¹ ⟩t t ≡ t' ∷ A / [Γ]
  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] =
    [Γ] , modelsTermEq [A] [t] [t]
                       (λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                              (proj₁ ([t] ⊢Δ [σ])))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t'] [t] [t'≡t] =
    [Γ] , modelsTermEq [A] [t] [t']
                       (λ ⊢Δ [σ] → symEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                             ([t'≡t] ⊢Δ [σ]))
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t')
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t'
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t')
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u]
    | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
      let [r]' = S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁
      in  [Γ] , modelsTermEq [A] [t] [r]'
                  (λ ⊢Δ [σ] →
                     let [σ]' = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                         [t≡u]₁' = irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ]'))
                                                     (proj₁ ([A] ⊢Δ [σ]))
                                                     ([t≡u]₁ ⊢Δ [σ]')
                     in  transEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                     ([t≡u] ⊢Δ [σ]) [t≡u]₁')
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A)
    with fundamentalTermEq t≡u | fundamentalEq A'≡A
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A)
    | [Γ] , modelsTermEq [A'] [t] [u] [t≡u] | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
      let [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A'] [A']₁ [t]
          [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A'] [A']₁ [u]
          [t]'' = convₛ {t} {A} {B} [Γ]₁ [A']₁ [A] [A'≡A] [t]'
          [u]'' = convₛ {u} {A} {B} [Γ]₁ [A']₁ [A] [A'≡A] [u]'
      in  [Γ]₁
      ,   modelsTermEq [A] [t]'' [u]''
            (λ ⊢Δ [σ] →
               let [σ]' = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                   [t≡u]' = irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]'))
                                              (proj₁ ([A']₁ ⊢Δ [σ]))
                                              ([t≡u] ⊢Δ [σ]')
               in  convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
                               ([A'≡A] ⊢Δ [σ]) [t≡u]')
  fundamentalTermEq (Π-cong {E} {F} {G} {H} ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]'  = Uₛ [Γ]
        [F]ₜ' = S.irrelevanceTerm {A = U} {t = F} [Γ]₁ [Γ] [U] [U]' [F]ₜ
        [H]ₜ' = S.irrelevanceTerm {A = U} {t = H} [Γ]₁ [Γ] [U] [U]' [H]ₜ
        [F]'  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = univₛ {A = H} [Γ] [U]' [H]ₜ'
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]' [F]
                  (univEqₛ {F} {H} [Γ]₁ [U] [F]' [F≡H]ₜ)
        [U]₁' = Uₛ (_∙_ {A = F} [Γ] [F])
        [U]₂' = Uₛ (_∙_ {A = H} [Γ] [H])
        [G]ₜ' = S.irrelevanceTerm {A = U} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {Δ} {σ} → [U]₁' {Δ} {σ}) [G]ₜ
        [E]ₜ' = S.irrelevanceTermLift {A = U} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {Δ} {σ} → [U]₁' {Δ} {σ})
                  (S.irrelevanceTerm {A = U} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {Δ} {σ} → [U]₁' {Δ} {σ}) [E]ₜ)
        [F≡H]ₜ' = S.irrelevanceEqTerm {A = U} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] (Uₛ [Γ]) [F≡H]ₜ
        [G≡E]ₜ' = S.irrelevanceEqTerm {A = U} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {Δ} {σ} → [U]₁' {Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [U]'
          (Πₜₛ {F} {G} [Γ] [F] (λ {Δ} {σ} → [U]₁' {Δ} {σ}) [F]ₜ' [G]ₜ')
          (Πₜₛ {H} {E} [Γ] [H] (λ {Δ} {σ} → [U]₂' {Δ} {σ}) [H]ₜ' [E]ₜ')
          (Π-congₜₛ {F} {G} {H} {E} [Γ] [F] [H]
                    (λ {Δ} {σ} → [U]₁' {Δ} {σ}) (λ {Δ} {σ} → [U]₂' {Δ} {σ})
                    [F]ₜ' [G]ₜ' [H]ₜ' [E]ₜ' [F≡H]ₜ' [G≡E]ₜ')
  fundamentalTermEq (app-cong {a} {b} {f} {g} {F} {G} f≡g a≡b)
    with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g]
      | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]' = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [f]' = S.irrelevanceTerm {A = Π F ▹ G} {t = f} [Γ] [Γ]₁ [ΠFG] [ΠFG]' [f]
        [g]' = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]' [g]
        [f≡g]' = S.irrelevanceEqTerm {A = Π F ▹ G} {t = f} {u = g}
                                     [Γ] [Γ]₁ [ΠFG] [ΠFG]' [f≡g]
        [G[a]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]' [a]
        [G[b]] = substSΠ {F} {G} {b} [Γ]₁ [F] [ΠFG]' [b]
        [G[a]≡G[b]] = substSΠEq {F} {G} {a} {b} [Γ]₁ [F] [ΠFG]' [a] [b] [a≡b]
    in  [Γ]₁ , modelsTermEq [G[a]]
                            (appₛ {F} {G} {f} {a} [Γ]₁ [F] [ΠFG]' [f]' [a])
                            (conv₂ₛ {g ∘ b} {G [ a ]} {G [ b ]} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appₛ {F} {G} {g} {b}
                                          [Γ]₁ [F] [ΠFG]' [g]' [b]))
                            (app-congₛ {F} {G} {f} {g} {a} {b}
                                       [Γ]₁ [F] [ΠFG]' [f≡g]' [a] [b] [a≡b])
  fundamentalTermEq (β-red {a} {b} {F} {G} ⊢F ⊢b ⊢a)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]' = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]' = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]' [b]
        [G[a]] = substS {F} {G} {a} [Γ]₂ [F]₁ [G]' [a]
        [b[a]] = substSTerm {F} {G} {a} {b} [Γ]₂ [F]₁ [G]' [b]' [a]
        [lam] , [eq] =
          redSubstTermₛ {G [ a ]} {(lam b) ∘ a} {b [ a ]} [Γ]₂
            (λ {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = wellformed (proj₁ ([F]₁ ⊢Δ [σ]))
                   ⊢σb = wellformedTerm (proj₁ ([G]' (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]' (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = wellformedTerm (proj₁ ([F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ (lam (subst (liftSubst σ) b))
                                          ∘ (subst σ a) ⇒ x ∷ y)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red ⊢σF ⊢σb ⊢σa))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (fun-ext {f} {g} {F} {G} ⊢F ⊢t ⊢t' t≡t') with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t' | fundamentalTermEq t≡t'
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t']
      | [Γ]₃ , modelsTermEq [G] [t0] [t'0] [t0≡t'0] =
    let [F]' = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]' = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]') [G]
        [t']' = S.irrelevanceTerm {A = Π F ▹ G} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t']
        [ΠFG]'' = Πₛ {F} {G} [Γ]₁ [F]' [G]'
        [t]'' = S.irrelevanceTerm {A = Π F ▹ G} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]'' [t]
        [t']'' = S.irrelevanceTerm {A = Π F ▹ G} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]'' [t']
        [t0≡t'0]' = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var zero}
                                        {u = wk1 g ∘ var zero}
                                        [Γ]₃ ([Γ]₁ ∙ [F]') [G] [G]' [t0≡t'0]
        [t≡t'] = fun-extₛ {f} {g} {F} {G} [Γ]₁ [F]' [G]' [t]'' [t']'' [t0≡t'0]'
        [t≡t']' = S.irrelevanceEqTerm {A = Π F ▹ G} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]'' [ΠFG] [t≡t']
    in  [Γ]₁ , modelsTermEq [ΠFG] [t] [t']' [t≡t']'
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucₛ {n = t} [Γ] [A] [t]
          [sucu] = sucₛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'}
                                 F≡F' z≡z' s≡s' n≡n')
    with fundamentalEq F≡F' |
         fundamentalTermEq z≡z'      |
         fundamentalTermEq s≡s'      |
         fundamentalTermEq n≡n'
  fundamentalTermEq (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'}
                                 F≡F' z≡z' s≡s' n≡n') |
    [Γ]  , [F] , [F'] , [F≡F'] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z'] [z≡z'] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s'] [s≡s'] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n'] [n≡n'] =
      let sType = Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
          s'Type = Π ℕ ▹ (F' ▹▹ F' [ suc (var zero) ]↑)
          [0] = S.irrelevanceTerm {l = ¹} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕₛ [Γ]₃) [ℕ] (zeroₛ [Γ]₃)
          [F]' = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F₀]' = S.irrelevance {A = F [ zero ]} [Γ]₁ [Γ]₃ [F₀]
          [F₊]' = S.irrelevance {A = sType} [Γ]₂ [Γ]₃ [F₊]
          [Fₙ]' = substS {ℕ} {F} {n} [Γ]₃ [ℕ] [F]' [n]
          [F']' = S.irrelevance {A = F'} [Γ] ([Γ]₃ ∙ [ℕ]) [F']
          [F₀]'' = substS {ℕ} {F} {zero} [Γ]₃ [ℕ] [F]' [0]
          [F'₀]' = substS {ℕ} {F'} {zero} [Γ]₃ [ℕ] [F']' [0]
          [F'₊]' = sucCase {F'} [Γ]₃ [ℕ] [F']'
          [F'ₙ']' = substS {ℕ} {F'} {n'} [Γ]₃ [ℕ] [F']' [n']
          [ℕ≡ℕ] = reflₛ {ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflₜₛ {ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F']' = S.irrelevanceEq {A = F} {B = F'}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]' [F≡F']
          [F₀≡F'₀] = substSEq {ℕ} {ℕ} {F} {F'} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]' [F']' [F≡F']' [0] [0] [0≡0]
          [F₀≡F'₀]' = S.irrelevanceEq {A = F [ zero ]} {B = F' [ zero ]}
                                      [Γ]₃ [Γ]₃ [F₀]'' [F₀]' [F₀≡F'₀]
          [F₊≡F'₊] = sucCaseCong {F} {F'} [Γ]₃ [ℕ] [F]' [F']' [F≡F']'
          [F₊≡F'₊]' = S.irrelevanceEq {A = sType} {B = s'Type}
                                      [Γ]₃ [Γ]₃ (sucCase {F} [Γ]₃ [ℕ] [F]')
                                      [F₊]' [F₊≡F'₊]
          [Fₙ≡F'ₙ']' = substSEq {ℕ} {ℕ} {F} {F'} {n} {n'}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]' [F']' [F≡F']'
                                [n] [n'] [n≡n']
          [z]' = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]' [z]
          [z']' = convₛ {z'} {F [ zero ]} {F' [ zero ]}
                        [Γ]₃ [F₀]' [F'₀]' [F₀≡F'₀]'
                        (S.irrelevanceTerm {A = F [ zero ]} {t = z'}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]' [z'])
          [z≡z']' = S.irrelevanceEqTerm {A = F [ zero ]} {t = z} {u = z'}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]' [z≡z']
          [s]' = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]₃ [F₊] [F₊]' [s]
          [s']' = convₛ {s'} {sType} {s'Type} [Γ]₃ [F₊]' [F'₊]' [F₊≡F'₊]'
                        (S.irrelevanceTerm {A = sType} {t = s'}
                                           [Γ]₂ [Γ]₃ [F₊] [F₊]' [s'])
          [s≡s']' = S.irrelevanceEqTerm {A = sType} {t = s} {u = s'}
                                        [Γ]₂ [Γ]₃ [F₊] [F₊]' [s≡s']
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]'
                       (natrecₛ {F} {z} {s} {n}
                                [Γ]₃ [ℕ] [F]' [F₀]' [F₊]' [Fₙ]' [z]' [s]' [n])
                       (conv₂ₛ {natrec F' z' s' n'} {F [ n ]} {F' [ n' ]}
                               [Γ]₃ [Fₙ]' [F'ₙ']' [Fₙ≡F'ₙ']'
                               (natrecₛ {F'} {z'} {s'} {n'}
                                        [Γ]₃ [ℕ] [F']' [F'₀]' [F'₊]' [F'ₙ']'
                                        [z']' [s']' [n']))
                       (natrec-congₛ {F} {F'} {z} {z'} {s} {s'} {n} {n'}
                                     [Γ]₃ [ℕ] [F]' [F']' [F≡F']'
                                     [F₀]' [F'₀]' [F₀≡F'₀]'
                                     [F₊]' [F'₊]' [F₊≡F'₊]' [Fₙ]'
                                     [z]' [z']' [z≡z']'
                                     [s]' [s']' [s≡s']' [n] [n'] [n≡n'])
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s) | [Γ] , [F]
    | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
        [Γ]' = [Γ]₁
        [ℕ]' = ℕₛ {l = ¹} [Γ]'
        [F₊]' = S.irrelevance {A = sType} [Γ]₂ [Γ]' [F₊]
        [s]' = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]' [F₊] [F₊]' [s]
        [F]' = S.irrelevance {A = F} [Γ] ([Γ]' ∙ [ℕ]') [F]
        d , r =
          redSubstTermₛ {F [ zero ]} {natrec F z s zero} {z} [Γ]'
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = wellformed (proj₁ ([ℕ]' ⊢Δ [σ]))
                   ⊢F = wellformed (proj₁ ([F]' (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]' ⊢Δ [ℕ]' [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x)
                                 (singleSubstLift F zero)
                                 (wellformedTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x)
                                 (natrecSucCase σ F)
                                 (wellformedTerm (proj₁ ([F₊]' ⊢Δ [σ]))
                                                (proj₁ ([s]' ⊢Δ [σ])))
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s zero)
                                    ⇒ subst σ z ∷ x)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]' , modelsTermEq [F₀] d [z] r
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]' = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]' = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]' [n]
        [sucn] = sucₛ {n = n} [Γ]₃ [ℕ]' [n]'
        [F₀]' = S.irrelevance {A = F [ zero ]} [Γ]₂ [Γ]₃ [F₀]
        [z]' = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                 [Γ]₂ [Γ]₃ [F₀] [F₀]' [z]
        [F]' = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]') [F]
        [F[sucn]] = substS {ℕ} {F} {suc n} [Γ]₃ [ℕ]' [F]' [sucn]
        [Fₙ]' = substS {ℕ} {F} {n} [Γ]₃ [ℕ]' [F]' [n]'
        [natrecₙ] = natrecₛ {F} {z} {s} {n}
                            [Γ]₃ [ℕ]' [F]' [F₀]' [F₊] [Fₙ]' [z]' [s] [n]'
        t = (s ∘ n) ∘ (natrec F z s n)
        q = subst (liftSubst (consSubst idSubst n))
                  (wk1 (F [ suc (var zero) ]↑))
        y = S.irrelevanceTerm'
              {A = q [ natrec F z s n ]} {A' = F [ suc n ]} {t = t}
              (natrecIrrelevantSubst' F z s n) [Γ]₃ [Γ]₃
              (substSΠ {F [ n ]} {q} {natrec F z s n} [Γ]₃
                (substS {ℕ} {F} {n} [Γ]₃ [ℕ]' [F]' [n]')
                (substSΠ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} {n}
                         [Γ]₃ [ℕ]' [F₊] [n]')
                [natrecₙ])
              [F[sucn]]
              (appₛ {F [ n ]} {q} {s ∘ n} {natrec F z s n} [Γ]₃ [Fₙ]'
                (substSΠ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} {n}
                         [Γ]₃ [ℕ]' [F₊] [n]')
                (appₛ {ℕ} {F ▹▹ F [ suc (var zero) ]↑} {s} {n}
                      [Γ]₃ [ℕ]' [F₊] [s] [n]')
                [natrecₙ])
        d , r =
          redSubstTermₛ {F [ suc n ]} {natrec F z s (suc n)} {t } {¹} {_} [Γ]₃
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢n = wellformedTerm (proj₁ ([ℕ]' ⊢Δ [σ]))
                                      (proj₁ ([n]' ⊢Δ [σ]))
                   ⊢ℕ = wellformed (proj₁ ([ℕ]' ⊢Δ [σ]))
                   ⊢F = wellformed (proj₁ ([F]' (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]₃ ⊢Δ [ℕ]' [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x)
                                 (singleSubstLift F zero)
                                 (wellformedTerm (proj₁ ([F₀]' ⊢Δ [σ]))
                                                (proj₁ ([z]' ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x)
                                 (natrecSucCase σ F)
                                 (wellformedTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                (proj₁ ([s] ⊢Δ [σ])))
                   r = _⊢_⇒_∷_.natrec-suc {n = subst σ n}
                                          {z = subst σ z} {s = subst σ s}
                                          {F = subst (liftSubst σ) F}
                                          ⊢n ⊢F ⊢z ⊢s
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s (suc n))
                                    ⇒ (subst σ t) ∷ x)
                           (PE.trans (PE.trans (substCompEq F)
                             (substEq (λ { zero → PE.refl
                                         ; (suc x) → PE.trans (subst-wk (σ x))
                                                              (substIdEq (σ x))
                                         })
                                      F))
                             (PE.sym (substCompEq F)))
                           r)
                        [F[sucn]] y
    in  [Γ]₃ , modelsTermEq [F[sucn]] d y r
