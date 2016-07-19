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
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊩ₛ⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]

  fundamentalℕ : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ]
  fundamentalℕ [Γ] ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ x₂ → id (ℕ ⊢Δ)

  fundamentalU : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) → Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ]
  fundamentalU [Γ] ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ x₂ → PE.refl

  fundamentalUniv : ∀ {A Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                    ([U] : Γ ⊩ₛ⟨ ¹ ⟩ U / [Γ])
                  → Γ ⊩ₛ⟨ ¹ ⟩t A ∷ U / [Γ] / [U]
                  → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]
  fundamentalUniv [Γ] [U] [A] ⊢Δ [σ] =
    let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
    in  [A]₁ , (λ x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x₁))

  fundamentalZero : ∀ {Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                  → Γ ⊩ₛ⟨ ¹ ⟩t zero ∷ ℕ / [Γ] / fundamentalℕ [Γ]
  fundamentalZero [Γ] ⊢Δ [σ] = ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ]
    , (λ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ])

  fundamentalSuc : ∀ {Γ n} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                   ([ℕ] : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
                 → Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ]
                 → Γ ⊩ₛ⟨ ¹ ⟩t suc n ∷ ℕ / [Γ] / [ℕ]
  fundamentalSuc ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
                            , (λ x → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x))

  fundamentalConv : ∀ {t A B Γ}
                    ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
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
    ,   λ [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ≡σ'])

-- Fundamental theorem for types

  fundamental : ∀ {Γ A} (⊢A : Γ ⊢ A) → Σ (⊩ₛ⟨ ¹ ⟩ Γ) (λ [Γ] → Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕ x) = valid x , fundamentalℕ (valid x)
  fundamental (U x) = valid x , fundamentalU (valid x)
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢F | fundamental ⊢G
  fundamental (Π_▹_ {F} {G} ⊢F ⊢G) | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , fundamentalΠ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , fundamentalUniv {A} [Γ] [U] [A]

-- Fundamental theorem for type equality

  fundamentalEq : ∀{Γ A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
    → ∃₂ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = fundamentalUniv {A} [Γ] [U] [t]
        [B] = fundamentalUniv {B} [Γ] [U] [u]
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
    [Γ] , fundamentalΠ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G])
        , fundamentalΠ {H} {E} [Γ] [H]
            (S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
              (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E]))
        , (λ {Δ} {σ} ⊢Δ [σ] → {!!})

-- Fundamental theorem for terms

  fundamentalTerm : ∀{Γ A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
    → ∃ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕ x) = valid x , fundamentalU (valid x)
                           , (λ ⊢Δ [σ] → let ⊢ℕ  = ℕ ⊢Δ
                                             [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                                         in  (⊢ℕ , [ℕ]) , (λ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ]))
  fundamentalTerm (Π ⊢F ▹ ⊢G) with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F] | [Γ]₁ , [U]₁ , [G] =
    [Γ] , [U] , {!!}
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , {!!}
  fundamentalTerm (lam {F} {G} ⊢F t) with fundamental ⊢F | fundamentalTerm t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] = [Γ] , fundamentalΠ {F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]) , {!!}
  fundamentalTerm (_∘_ {g} {a} {F} {G} Dt Du) with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]' = S.irrelevance {A = Π F ▹ G} [Γ] [Γ]₁ [ΠFG]
    in  [Γ]₁ , substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]' [u] , {!!}
  fundamentalTerm (zero x) = valid x , fundamentalℕ (valid x) , fundamentalZero (valid x)
  fundamentalTerm (suc {n} t) with fundamentalTerm t
  fundamentalTerm (suc {n} t) | [Γ] , [ℕ] , [n] = [Γ] , [ℕ] , fundamentalSuc {n = n} [Γ] [ℕ] [n]
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
                    → ∃ λ ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
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
    [Γ] , modelsTermEq [A] (fundamentalSuc {n = t} [Γ] [A] [t])
                     (fundamentalSuc {n = u} [Γ] [A] [u])
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
        [ℕ]' = fundamentalℕ [Γ]'
        [F]' = S.irrelevance {A = F} [Γ] ([Γ]' ∙ [ℕ]') [F]
    in  [Γ]' , modelsTermEq [F₀] (fundamentalNatrec [Γ]' [ℕ]' [F]' {!!} {!!} {!!} {!!} {!!} (fundamentalZero [Γ]₁)) [z] {!!}
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s) with fundamentalTerm ⊢n | fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]' = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]' = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]' [n]
        [sucn] = fundamentalSuc {n = n} [Γ]₃ [ℕ]' [n]'
        [F]' = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]') [F]
        [F[sucn]] = substS {ℕ} {F} {suc n} [Γ]₃ [ℕ]' [F]' [sucn]
    in  [Γ]₃ , modelsTermEq [F[sucn]] {!!} {!!} {!!}

  fundamentalΠ : ∀ {F G Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                 ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
               → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F]
               → Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ]
  fundamentalΠ {F} {G} {Γ} [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
    let [F]σ {σ'} [σ'] = [F] {σ = σ'} ⊢Δ [σ']
        [σF] = proj₁ ([F]σ [σ])
        ⊢F {σ'} [σ'] = soundness (proj₁ ([F]σ {σ'} [σ']))
        [G]σ {σ'} [σ'] = [G] {σ = liftSubst σ'} (⊢Δ ∙ ⊢F [σ'])
                             (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ'])
        ⊢G {σ'} [σ'] = soundness (proj₁ ([G]σ {σ'} [σ']))
        ⊢ΠF▹G = Π ⊢F [σ] ▹ ⊢G [σ]
        [G]a : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
               ([a] : Δ₁ ⊩⟨ ¹ ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                  / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])))
             → Σ (Δ₁ ⊩⟨ ¹ ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G)
                 (λ [Aσ] →
                 {σ' : Nat → Term} →
                 Δ₁ ⊩ₛ⟨ ¹ ⟩ consSubst (wkSubst (T.toWk ρ) σ) a ≡ σ' ∷ Γ ∙ F /
                 [Γ] ∙ [F] / ⊢Δ₁ /
                 consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) [F]
                 [a] →
                 Δ₁ ⊩⟨ ¹ ⟩ subst (consSubst (wkSubst (T.toWk ρ) σ) a) G ≡
                 subst σ' G / [Aσ])
        [G]a a ρ ⊢Δ₁ [a] = ([G] {σ = consSubst (wkSubst (T.toWk ρ) σ) a} ⊢Δ₁
                                (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                            (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                            [F] [a]))
        [G]a' : ∀ {Δ₁} a (ρ : Δ T.⊆ Δ₁) (⊢Δ₁ : ⊢ Δ₁)
              → Δ₁ ⊩⟨ ¹ ⟩ a ∷ subst (wkSubst (T.toWk ρ) σ) F
                   / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))
              → Δ₁ ⊩⟨ ¹ ⟩ T.wkLiftₜ ρ (subst (liftSubst σ) G) [ a ]
        [G]a' a ρ ⊢Δ₁ [a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (G-substWkLemma a σ G))
                                     (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
    in Π (idRed:*: ⊢ΠF▹G) (⊢F [σ]) (⊢G [σ]) (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
           let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
           in  [G]a' a ρ ⊢Δ₁ [a]')
        (λ {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [a≡b] →
           let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
               [a≡b]' = irrelevanceEqTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                     (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a≡b]
           in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                               (PE.sym (G-substWkLemma b σ G))
                               (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                               ([G]a' a ρ ⊢Δ₁ [a]')
                               (proj₂ ([G]a a ρ ⊢Δ₁ [a]')
                                      (reflSubst [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]) , [a≡b]')))
    ,  (λ {σ'} [σ≡σ'] →
           let [σ'] : Δ ⊩ₛ⟨ ¹ ⟩ σ' ∷ Γ / [Γ] / ⊢Δ
               [σ'] = {!!}
               var0 = var (⊢Δ ∙ ⊢F [σ])
                          (PE.subst (λ x → zero ∷ x ∈ (Δ ∙ subst σ F))
                                    (wk-subst F) here)
           in  Π¹[ _ , _ , id (Π ⊢F [σ'] ▹ ⊢G [σ'])
               , Π-cong (⊢F [σ]) (soundnessEq (proj₁ ([F] ⊢Δ [σ])) (proj₂ ([F] ⊢Δ [σ]) [σ≡σ']))
                           (soundnessEq (proj₁ ([G]σ [σ]))
                                        (proj₂ ([G]σ [σ])
                                        (wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ']
                                          , neuEqTerm (proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) (wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ])))
                                                      (var zero) (var zero) (var0 , var0 , refl var0))))
               , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ≡σ']))
               , (λ {Δ₁} {a} ρ ⊢Δ₁ [a] →
                    let [a]' = irrelevanceTerm' (wk-subst F) (wk ρ ⊢Δ₁ [σF])
                                   (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]))) [a]
                        [ρσa≡ρσ'a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                  (wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ])
                                                  (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ']) [F] [a]'
                    in  irrelevanceEq'' (PE.sym (G-substWkLemma a σ G))
                                        (PE.sym (G-substWkLemma a σ' G))
                                        (proj₁ ([G]a a ρ ⊢Δ₁ [a]'))
                                        ([G]a' a ρ ⊢Δ₁ [a]')
                                        (proj₂ ([G]a a ρ ⊢Δ₁ [a]') [ρσa≡ρσ'a]))
               ])

  substS : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
           ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
           ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
         → Γ ⊩ₛ⟨ ¹ ⟩ G [ t ] / [Γ]
  substS {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
    let G[t] = (proj₁ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ
                      (consSubstS {t = subst σ t} {A = F} [Γ] ⊢Δ [σ] [F] (proj₁ ([t] ⊢Δ [σ])))))
        G[t]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                        G[t]

    in  G[t]' , (λ [σ≡σ'] → irrelevanceEq'' (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                                            (PE.sym (PE.trans (substCompEq G) (substEq substConcatSingleton' G)))
                                            G[t] G[t]' (proj₂ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ
                      (consSubstS {t = subst σ t} {A = F} [Γ] ⊢Δ [σ] [F] (proj₁ ([t] ⊢Δ [σ])))) ([σ≡σ'] , (proj₂ ([t] ⊢Δ [σ]) [σ≡σ']))))

  substSΠ : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
            ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ ¹ ⟩ G [ t ] / [Γ]
  substSΠ [Γ] [F] [ΠFG] [t] ⊢Δ [σ] = {!!}

  subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
          → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
  subst↑S [Γ] [F] [G] [t] ⊢Δ [σ] = {!!}

  fundamentalNatrec : ∀ {F z s n Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                      ([ℕ]  : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
                      ([F]  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F / [Γ] ∙ [ℕ])
                      ([F₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] / [Γ])
                      ([F₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
                      ([Fₙ] : Γ ⊩ₛ⟨ ¹ ⟩ F [ n ] / [Γ])
                    → Γ ⊩ₛ⟨ ¹ ⟩t z ∷ F [ zero ] / [Γ] / [F₀]
                    → Γ ⊩ₛ⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊]
                    → ([n] : Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ])
                    → Γ ⊩ₛ⟨ ¹ ⟩t natrec F z s n ∷ F [ n ] / [Γ] / [Fₙ]
  fundamentalNatrec [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n] ⊢Δ [σ] = {!!}

  Π-injectivity₁ : ∀ {Γ F G}
                   ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                 → Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ]
                 → Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ]
  Π-injectivity₁ [Γ] [ΠFG] ⊢Δ [σ] with proj₁ ([ΠFG] ⊢Δ [σ])
  Π-injectivity₁ [Γ] [ΠFG] ⊢Δ [σ] | ℕ D = {!!}
  Π-injectivity₁ [Γ] [ΠFG] ⊢Δ [σ] | ne D neK = {!!}
  Π-injectivity₁ [Γ] [ΠFG] ⊢Δ [σ] | Π D ⊢F ⊢G [F] [G] G-ext =
    let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
    in  PE.subst (λ x → _ ⊩⟨ _ ⟩ x) (PE.trans (wk-id _ zero) (PE.sym F≡F')) ([F] T.base ⊢Δ) , (λ x → {!!})
  Π-injectivity₁ [Γ] [ΠFG] ⊢Δ [σ] | emb x = {!!}
