module Lemma.Fundamental where

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
open import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊩ₛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]

  fundamentalConv : ∀ {t A B Γ}
                    ([Γ] : ⊩ₛ Γ)
                    ([A]  : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
                    ([B]  : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
                  → Γ ⊩ₛ⟨ ¹ ⟩  A ≡ B / [Γ] / [A]
                  → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
                  → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ B / [Γ] / [B]
  fundamentalConv [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
    let [σA]     = proj₁ ([A] ⊢Δ [σ])
        [σB]     = proj₁ ([B] ⊢Δ [σ])
        [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
        [σt]     = proj₁ ([t] ⊢Δ [σ])
        [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
    in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
    ,   λ [σ'] [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ'] [σ≡σ'])

-- Fundamental theorem for types

  fundamental : ∀ {Γ A} (⊢A : Γ ⊢ A) → Σ (⊩ₛ Γ) (λ [Γ] → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕ x) = valid x , ℕₛ (valid x)
  fundamental (U x) = valid x , Uₛ (valid x)
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢F | fundamental ⊢G
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , Πₛ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , univₛ₁ {A} [Γ] [U] [A]

-- Fundamental theorem for type equality

  fundamentalEq : ∀{Γ A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ₛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = univₛ₁ {A} [Γ] [U] [t]
        [B] = univₛ₁ {B} [Γ] [U] [u]
    in  [Γ] , [A] , [B] , (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) = let [Γ] , [B] = fundamental D
                           in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] = [Γ] , [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans {A} {B₁} {B} A≡B₁ B₁≡B) with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {A} {B₁} {B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁] | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
    [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
        , (λ ⊢Δ [σ] →
             let [σ]' = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
             in  transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                         (proj₁ ([B] ⊢Δ [σ]')) ([A≡B₁] ⊢Δ [σ])
                         (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ]'))
                                        (proj₁ ([B₁] ⊢Δ [σ]))
                                        ([B₁≡B] ⊢Δ [σ]')))
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [Γ] , [F] , [H] , [F≡H] | [Γ]₁ , [G] , [E] , [G≡E] =
    [Γ] , Πₛ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G])
        , Πₛ {H} {E} [Γ] [H]
            (S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
              (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E]))
        , (λ {Δ} {σ} ⊢Δ [σ] → Π¹[ {!!} , {!!} , {!!} , {!!} , {!!} , {!!} ])

  fundamentalVar : ∀ {Γ A x}
                 → x ∷ A ∈ Γ
                 → ([Γ] : ⊩ₛ Γ)
                 → ∃ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
                 → Γ ⊩ₛ⟨ ¹ ⟩t var x ∷ A / [Γ] / [A]
  fundamentalVar here (_∙_ {A = A} {l = l} [Γ] [A]) =
    (λ ⊢Δ [σ] →
       let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
           [σA'] = maybeEmb (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (subst-wk A)) [σA])
       in  [σA']
       ,   (λ [σ'] [σ≡σ'] →
              irrelevanceEq'' (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA'] (proj₂ ([A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ']) (proj₁ [σ≡σ']))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
             [σA'] = maybeEmb (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm' (PE.sym (subst-wk A)) [σA] [σA'] (proj₂ [σ])
    , (λ [σ'] [σ≡σ'] → irrelevanceEqTerm' (PE.sym (subst-wk A)) [σA] [σA'] (proj₂ [σ≡σ'])))
  fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (λ ⊢Δ [σ] →
       let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA'] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (subst-wk A)) [σA]
       in  [σA']
       ,   (λ [σ'] [σ≡σ'] →
              irrelevanceEq'' (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA'] (proj₂ [h] (proj₁ [σ']) (proj₁ [σ≡σ']))))
    , (λ ⊢Δ [σ] →
         let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA'] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (subst-wk A)) [σA]
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
  fundamentalTerm (Π_▹_ {F} {G} ⊢F ⊢G) with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univₛ {F} [Γ] [U] [F]ₜ
        [U]'  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ' = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uₛ [Γ]) [F]ₜ
        [G]ₜ' = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁ (λ {Δ} {σ} → [U]' {Δ} {σ}) [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Π F ▹ G} [Γ] [Γ] (Uₛ [Γ]) [U]
                          (Πₜₛ {F} {G} [Γ] [F] (λ {Δ} {σ} → [U]' {Δ} {σ}) [F]ₜ' [G]ₜ')
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lam {F} {G} {t} ⊢F ⊢t) with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]' = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]' = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]' [t]
    in  [Γ] , Πₛ {F} {G} [Γ] [F] [G]'
    ,   lamₛ {F} {G} {t} [Γ] [F] [G]' [t]'
  fundamentalTerm (_∘_ {g} {a} {F} {G} Dt Du) with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]' = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [t]' = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]' [t]
    in  [Γ]₁ , substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]' [u] , appₛ {F} {G} {g} {a} [Γ]₁ [F] [ΠFG]' [t]' [u]
  fundamentalTerm (zero x) = valid x , ℕₛ (valid x) , zeroₛ (valid x)
  fundamentalTerm (suc {n} t) with fundamentalTerm t
  fundamentalTerm (suc {n} t) | [Γ] , [ℕ] , [n] = [Γ] , [ℕ] , sucₛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrec {G} {s} {z} {n} ⊢G ⊢z ⊢s ⊢n) with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let [Γ]' = [Γ]₃
        [G]' = S.irrelevance {A = G} [Γ] ([Γ]₃ ∙ [ℕ]) [G]
    in  [Γ]' , substS {F = ℕ} {G = G} {t = n} [Γ]' [ℕ] [G]' [n]
    ,   (λ ⊢Δ [σ] → {!!})
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A) with fundamentalTerm ⊢t | fundamentalEq A'≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A) | [Γ] , [A'] , [t] | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
    let [Γ]' = [Γ]₁
        [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]' [A'] [A']₁ [t]
    in  [Γ]' , [A]
    ,   fundamentalConv {t} {A} {B} [Γ]' [A']₁ [A] [A'≡A] [t]'

-- Fundamental theorem for term equality

  fundamentalTermEq : ∀{Γ A t t'} → Γ ⊢ t ≡ t' ∷ A
                    → ∃ λ ([Γ] : ⊩ₛ Γ)
                    → Γ ⊩ₛ⟨ ¹ ⟩t t ≡ t' ∷ A / [Γ]
  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] = [Γ] , modelsTermEq [A] [t] [t] λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t'] [t] [t'≡t] = [Γ] , modelsTermEq [A] [t] [t'] λ ⊢Δ [σ] →
      symEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t'≡t] ⊢Δ [σ])
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t') with fundamentalTermEq t≡u | fundamentalTermEq u≡t'
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t') | [Γ] , modelsTermEq [A] [t] [u] [t≡u] | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
    [Γ] , modelsTermEq [A] [t]
                 (S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁)
                 (λ ⊢Δ [σ] → let [σ]' = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                             in  transEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
                                             (irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ]')) (proj₁ ([A] ⊢Δ [σ])) ([t≡u]₁ ⊢Δ [σ]')))
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A) with fundamentalTermEq t≡u | fundamentalEq A'≡A
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A) | [Γ] , modelsTermEq [A'] [t] [u] [t≡u] | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
    let [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A'] [A']₁ [t]
        [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A'] [A']₁ [u]
    in  [Γ]₁
    ,   modelsTermEq [A]
                     (fundamentalConv {t} {A} {B} [Γ]₁ [A']₁ [A] [A'≡A] [t]')
                     (fundamentalConv {u} {A} {B} [Γ]₁ [A']₁ [A] [A'≡A] [u]')
                     (λ ⊢Δ [σ]₁ → let [σ] = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]₁
                                in  convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ]₁)) (proj₁ ([A] ⊢Δ [σ]₁)) ([A'≡A] ⊢Δ [σ]₁)
                                                (irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                                   (proj₁ ([A']₁ ⊢Δ [σ]₁))
                                                                   ([t≡u] ⊢Δ [σ])))
  fundamentalTermEq (Π-cong ⊢F F≡H G≡E) with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]₁ [G] [F≡G] | [Γ]₂ , modelsTermEq [U]₁ [F]₂ [G]₁ [F≡G]₁ =
    [Γ]₁ , modelsTermEq [U] {!!} {!!} {!!}
  fundamentalTermEq (app-cong {a} {b} {f} {g} {F} {G} f≡g a≡b) with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g] | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]' = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
    in  [Γ]₁ , modelsTermEq (substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]' [a]) {!!} {!!} {!!}
  fundamentalTermEq (β-red {a} {b} {F} {G} ⊢F ⊢b ⊢a) with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]' = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
    in  [Γ]₂ , modelsTermEq (substS {F} {G} {a} [Γ]₂ [F]₁ [G]' [a]) {!!} {!!} {!!}
  fundamentalTermEq (fun-ext {f} {g} {F} {G} ⊢F ⊢t ⊢t' t≡t') with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t' | fundamentalTermEq t≡t'
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t'] | [Γ]₃ , modelsTermEq [G] [t0] [t'0] [t≡t'] =
    let [t']' = S.irrelevanceTerm {A = Π F ▹ G} {t = g} [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t']
    in  [Γ]₁ , modelsTermEq [ΠFG] [t] [t']' {!!}
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x) | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
    [Γ] , modelsTermEq [A] (sucₛ {n = t} [Γ] [A] [t])
                     (sucₛ {n = u} [Γ] [A] [u])
                     (λ ⊢Δ [σ] → sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'} F≡F' z≡z' s≡s' n≡n')
    with fundamentalEq F≡F' |
         fundamentalTermEq z≡z'      |
         fundamentalTermEq s≡s'      |
         fundamentalTermEq n≡n'
  fundamentalTermEq (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'} F≡F' z≡z' s≡s' n≡n') |
    [Γ]  , [F] , [F'] , [F≡F'] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z'] [z≡z'] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s'] [s≡s'] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n'] [n≡n'] =
    [Γ]₃ , modelsTermEq (substS {ℕ} {F} {n} [Γ]₃ [ℕ] (S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]) [n])
                 {!fundamentalNatrec {F} {z} {s} {n} ? [ℕ] [F] [F₀] [F₊] {!!} [z] [s] [n]!}
                 {!fundamentalNatrec {F'} {z'} {s'} {n'} ? [ℕ] [F'] {![F₀]!} {![F₊]!} {!!} [z'] [s'] [n']!}
                 (λ ⊢Δ [σ] → {!!})
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s) with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s) | [Γ] , [F] | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let [Γ]' = [Γ]₁
        [ℕ]' = ℕₛ {l = ¹} [Γ]'
        [F]' = S.irrelevance {A = F} [Γ] ([Γ]' ∙ [ℕ]') [F]
    in  [Γ]' , modelsTermEq [F₀] {!fundamentalNatrec [Γ]' [ℕ]' [F]' {!!} {!!} {!!} {!!} {!!} (zeroₛ [Γ]₁)!} [z] {!!}
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s) with fundamentalTerm ⊢n | fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]' = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]' = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]' [n]
        [sucn] = sucₛ {n = n} [Γ]₃ [ℕ]' [n]'
        [F]' = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]') [F]
        [F[sucn]] = substS {ℕ} {F} {suc n} [Γ]₃ [ℕ]' [F]' [sucn]
    in  [Γ]₃ , modelsTermEq [F[sucn]] {!!} {!!} {!!}
