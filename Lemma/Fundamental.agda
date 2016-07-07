module Lemma.Fundamental where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
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

  fundamentalConv : ∀ {t A B Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                    ([A] [A'] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
                    ([B] : Γ ⊩ₛ⟨ ¹ ⟩ B / [Γ])
                  → Γ ⊩ₛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A']
                  → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
                  → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ B / [Γ] / [B]
  fundamentalConv ⊢Γ [A] [A'] [B] [A≡B] [t] ⊢Δ [σ] =
    let [σA]     = proj₁ ([A] ⊢Δ [σ])
        [σA']    = proj₁ ([A'] ⊢Δ [σ])
        [σB]     = proj₁ ([B] ⊢Δ [σ])
        [σA≡σB]  = irrelevanceEq [σA'] [σA] ([A≡B] ⊢Δ [σ])
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
    [Γ] , fundamentalΠ {F} {G} [Γ] [F] {![G]!}
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
    in  {!!} , [A] , [B] , (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) = let [Γ] , [B] = fundamental D
                           in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] = [Γ] , [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans A≡B₁ B₁≡B) with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁] | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
    [Γ] , [A] , {![B]!}
        , (λ ⊢Δ [σ] → transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                              (proj₁ ([B] ⊢Δ {![σ]!})) ([A≡B₁] ⊢Δ [σ])
                              (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ {![σ]!}))
                                                   (proj₁ ([B₁] ⊢Δ [σ]))
                                                   ([B₁≡B] ⊢Δ {![σ]!})))
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [Γ] , [F] , [H] , [F≡H] | [Γ]₁ , [G] , [E] , [G≡E] =
    [Γ] , fundamentalΠ {F} {G} [Γ] [F] {![G]!} , fundamentalΠ {H} {E} {!!} [H] {![E]!} , {!!}

-- Fundamental theorem for terms

  fundamentalTerm : ∀{Γ A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
    → ∃ λ ([A] : Γ ⊩ₛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ₛ⟨ ¹ ⟩t t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕ x) = valid x , fundamentalU (valid x)
                           , (λ ⊢Δ [σ] → let ⊢ℕ  = ℕ ⊢Δ
                                             [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                                         in  (⊢ℕ , [ℕ]) , (λ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ]))
  fundamentalTerm (Π x ▹ x₁) = {!!}
  fundamentalTerm (var x₁ x₂) = {!!}
  fundamentalTerm (lam {F} {G} ⊢F t) with fundamental ⊢F | fundamentalTerm t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] = [Γ] , fundamentalΠ {F} {G} [Γ] [F] {![G]!} , {!!}
  fundamentalTerm (Dt ∘ Du) with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠAB] , [t] | [Γ]₁ , [A] , [u] = {!!}
  fundamentalTerm (zero x) = valid x , fundamentalℕ (valid x) , fundamentalZero (valid x)
  fundamentalTerm (suc {n} t) with fundamentalTerm t
  fundamentalTerm (suc {n} t) | [Γ] , [ℕ] , [n] = [Γ] , [ℕ] , fundamentalSuc {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrec x x₁ x₂ x₃) = {!!}
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A) with fundamentalTerm ⊢t | fundamentalEq A'≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A'≡A) | [Γ] , [A'] , [t] | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
    {!!} , [A] , {!fundamentalConv {t} {A} {B} ? [A'] [A']₁ [A] [A'≡A] [t]!}

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
                 (λ ⊢Δ [σ] → transEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
                                         (irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ {![σ]!})) (proj₁ ([A] ⊢Δ [σ])) ([t≡u]₁ ⊢Δ {![σ]!})))
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A) with fundamentalTermEq t≡u | fundamentalEq A'≡A
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A'≡A) | [Γ] , modelsTermEq [A'] [t] [u] [t≡u] | [Γ]₁ , [A']₁ , [A] , [A'≡A] =
    [Γ] , {!modelsTermEq [A] (fundamentalConv {t} {A} {B} [A'] [A']₁ [A] [A'≡A] [t])
                     (fundamentalConv {u} {A} {B} [A'] [A']₁ [A] [A'≡A] [u])
                     (λ ⊢Δ [σ] → convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([A'≡A] ⊢Δ [σ])
                                             (irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                                      (proj₁ ([A']₁ ⊢Δ [σ]))
                                                                      ([t≡u] ⊢Δ [σ])))!}
  fundamentalTermEq (Π-cong x x₁ x₂) = {!!}
  fundamentalTermEq (app-cong x x₁) = {!!}
  fundamentalTermEq (β-red x x₁ x₂) = {!!}
  fundamentalTermEq (fun-ext x x₁ x₂ x₃) = {!!}
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
    {!!} , modelsTermEq {!substS {ℕ} {F} {n} ? (ℕ ?) [ℕ] [F] [n]!}
                 {!fundamentalNatrec {F} {z} {s} {n} ? [ℕ] [F] [F₀] [F₊] {!!} [z] [s] [n]!}
                 {!fundamentalNatrec {F'} {z'} {s'} {n'} ? [ℕ] [F'] {![F₀]!} {![F₊]!} {!!} [z'] [s'] [n']!}
                 (λ ⊢Δ [σ] → {!!})
  fundamentalTermEq (natrec-zero F z s) with fundamental F | fundamentalTerm z | fundamentalTerm s
  fundamentalTermEq (natrec-zero F z s) | [Γ] , [F] | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [s] =
    {!!} , modelsTermEq [F₀] {!!} [z] {!!}
  fundamentalTermEq (natrec-suc n F z s) = {!!}

  fundamentalΠ : ∀ {F G Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ) ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
               → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F]
               → Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ]
  fundamentalΠ [Γ] [F] [G] ⊢Δ [σ] =
    let ⊢F    = soundness (proj₁ ([F] ⊢Δ [σ]))
        ⊢G    = soundness (proj₁ ([G] (⊢Δ ∙ ⊢F) ({!!} , {!!})))
        ⊢ΠF▹G = Π ⊢F ▹ ⊢G
        [σF]  = proj₁ ([F] ⊢Δ [σ])
        [σG]  = proj₁ ([G] (⊢Δ ∙ ⊢F) {!!})
    in  Π (idRed:*: ⊢ΠF▹G) ⊢F ⊢G (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF]) (λ ρ ⊢Δ₁ x → {!!}) (λ ρ ⊢Δ₁ [a] x → {!!})
    ,   (λ x → Π¹[ _ , _ , id {!⊢ΠF▹G!} , {!!} , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] {!!}) , (λ ρ ⊢Δ₁ [a] → {!!}) ])

  substS : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
           ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
           ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
         → Γ ⊩ₛ⟨ ¹ ⟩ G [ t ] / [Γ]
  substS [Γ] [F] [G] [t] ⊢Δ [σ] = {!!}

  subst↑S : ∀ {F G t Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ F / [Γ] / [F])
          → Γ ∙ F ⊩ₛ⟨ ¹ ⟩ G [ t ]↑ / [Γ] ∙ [F]
  subst↑S ⊢Γ [F] [G] [t] ⊢Δ [σ] = {!!}

  fundamentalNatrec : ∀ {F z s n Γ} ([Γ] : ⊩ₛ⟨ ¹ ⟩ Γ)
                      ([ℕ]  : Γ ⊩ₛ⟨ ¹ ⟩ ℕ / [Γ])
                      ([F]  : Γ ∙ ℕ ⊩ₛ⟨ ¹ ⟩ F / [Γ] ∙ [ℕ])
                      ([F₀] : Γ ⊩ₛ⟨ ¹ ⟩ F [ zero ] / [Γ])
                      ([F₊] : Γ ⊩ₛ⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ])
                      ([Fₙ] : Γ ⊩ₛ⟨ ¹ ⟩ F [ n ] / [Γ])
                    → Γ ⊩ₛ⟨ ¹ ⟩t z ∷ F [ zero ] / [Γ] / [F₀]
                    → Γ ⊩ₛ⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / [Γ] / [F₊]
                    → ([n] : Γ ⊩ₛ⟨ ¹ ⟩t n ∷ ℕ / [Γ] / [ℕ])
                    → Γ ⊩ₛ⟨ ¹ ⟩t natrec F z s n ∷ F [ n ] / [Γ] / substS {ℕ} {F} {n} [Γ] [ℕ] [F] [n]
  fundamentalNatrec = {!!}
