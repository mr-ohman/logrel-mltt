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

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat renaming (ℕ to Nat)

import Relation.Binary.PropositionalEquality as PE


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamentalℕ : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ
  fundamentalℕ ⊢Γ ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ x₂ → id (ℕ ⊢Δ)

  fundamentalU : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ U / valid ⊢Γ
  fundamentalU ⊢Γ ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ x₂ → PE.refl

  fundamentalUniv : ∀ {A Γ} (⊢Γ : ⊢ Γ)
                    ([U] : Γ ⊨⟨ ¹ ⟩ U / valid ⊢Γ)
                  → Γ ⊨⟨ ¹ ⟩t A ∷ U / valid ⊢Γ / [U] → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamentalUniv ⊢Γ [U] [A] ⊢Δ [σ] =
    let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
    in  [A]₁ , (λ x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x₁))

  fundamentalZero : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩t zero ∷ ℕ / valid ⊢Γ / fundamentalℕ ⊢Γ
  fundamentalZero ⊢Γ ⊢Δ [σ] = ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ]
    , (λ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ])

  fundamentalSuc : ∀ {Γ n} (⊢Γ : ⊢ Γ)
                   ([ℕ] : Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ)
                 → Γ ⊨⟨ ¹ ⟩t n ∷ ℕ / valid ⊢Γ / [ℕ] → Γ ⊨⟨ ¹ ⟩t suc n ∷ ℕ / valid ⊢Γ / [ℕ]
  fundamentalSuc ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
                            , (λ x → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x))

  fundamentalConv : ∀ {t A B Γ} (⊢Γ : ⊢ Γ)
                    ([A] [A'] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ)
                    ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ)
                  → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A']
                  → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
                  → Γ ⊨⟨ ¹ ⟩t t ∷ B / valid ⊢Γ / [B]
  fundamentalConv ⊢Γ [A] [A'] [B] [A≡B] [t] ⊢Δ [σ] =
    let [σA]     = proj₁ ([A] ⊢Δ [σ])
        [σA']    = proj₁ ([A'] ⊢Δ [σ])
        [σB]     = proj₁ ([B] ⊢Δ [σ])
        [σA≡σB]  = proof-irrelevanceEq [σA'] [σA] ([A≡B] ⊢Δ [σ])
        [σt]     = proj₁ ([t] ⊢Δ [σ])
        [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
    in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
    ,   λ [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ≡σ'])

  proof-irrelevanceTermS : ∀ {A t Γ} (⊢Γ : ⊢ Γ) ([A] [A]' : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ)
                         → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A] → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]'
  proof-irrelevanceTermS ⊢Γ [A] [A]' [t] ⊢Δ [σ] =
    let [σA]  = proj₁ ([A] ⊢Δ [σ])
        [σA]' = proj₁ ([A]' ⊢Δ [σ])
    in  (proof-irrelevanceTerm [σA] [σA]' (proj₁ ([t] ⊢Δ [σ]))) , (λ x → proof-irrelevanceEqTerm [σA] [σA]' ((proj₂ ([t] ⊢Δ [σ])) x))

-- Fundamental theorem for types

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) = fundamentalℕ ⊢Γ
  fundamental ⊢Γ (U x) = fundamentalU ⊢Γ
  fundamental ⊢Γ (Π_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢Γ ⊢F | fundamental (⊢Γ ∙ ⊢F) ⊢G
  ... | [F] | [G] = fundamentalΠ {F} {G} ⊢Γ [F] [G]
  fundamental ⊢Γ (univ {A} ⊢A) with fundamentalTerm ⊢Γ ⊢A
  fundamental ⊢Γ (univ {A} ⊢A) | [U] , [A] = fundamentalUniv {A} ⊢Γ [U] [A]

-- Fundamental theorem for type equality

  fundamentalEq : ∀{Γ A B}  (⊢Γ : ⊢ Γ) → Γ ⊢ A ≡ B
    → ∃₂ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ)
    → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A]
  fundamentalEq ⊢Γ (univ {A} {B} x) with fundamentalTermEq ⊢Γ x
  fundamentalEq ⊢Γ (univ {A} {B} x) | modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = fundamentalUniv {A} ⊢Γ [U] [t]
        [B] = fundamentalUniv {B} ⊢Γ [U] [u]
    in  [A] , [B] , (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalEq ⊢Γ (refl D) = let [B] = fundamental ⊢Γ D
                              in  [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (sym A≡B) with fundamentalEq ⊢Γ A≡B
  fundamentalEq ⊢Γ (sym A≡B) | [B] , [A] , [B≡A] = [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq ⊢Γ (trans A≡B₁ B₁≡B) with fundamentalEq ⊢Γ A≡B₁ | fundamentalEq ⊢Γ B₁≡B
  fundamentalEq ⊢Γ (trans A≡B B≡C) | [A] , [B₁] , [A≡B₁] | [B₁]₁ , [B] , [B₁≡B] =
    [A] , [B] , (λ ⊢Δ [σ] → transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) ([A≡B₁] ⊢Δ [σ]) (proof-irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) ([B₁≡B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) with fundamentalEq ⊢Γ A≡B | fundamentalEq (⊢Γ ∙ ⊢F) A≡B₁
  fundamentalEq ⊢Γ (Π-cong {F} {H} {G} {E} ⊢F A≡B A≡B₁) | [F] , [H] , [F≡H] | [G] , [E] , [G≡E] =
    fundamentalΠ {F} {G} ⊢Γ [F] {![G]!} , fundamentalΠ {H} {E} ⊢Γ [H] {![E]!} , {!!}

-- Fundamental theorem for terms

  fundamentalTerm : ∀{Γ A t}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ∷ A →
    ∃ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
  fundamentalTerm ⊢Γ (ℕ x) = fundamentalU ⊢Γ
                           , (λ ⊢Δ [σ] → let ⊢ℕ  = ℕ ⊢Δ
                                             [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                                         in  (⊢ℕ , [ℕ]) , (λ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ]))
  fundamentalTerm ⊢Γ (Π x ▹ x₁) = fundamentalU ⊢Γ , {!!}
  fundamentalTerm ⊢Γ (var x₁ x₂) = {!!}
  fundamentalTerm ⊢Γ (lam {F} {G} ⊢F t) with fundamental ⊢Γ ⊢F | fundamentalTerm (⊢Γ ∙ ⊢F) t
  ... | [F] | [G] , [t] = fundamentalΠ {F} {G} ⊢Γ [F] [G] , {!!}
  fundamentalTerm ⊢Γ (Dt ∘ Du) with fundamentalTerm ⊢Γ Dt | fundamentalTerm ⊢Γ Du
  ... | [ΠAB] , [t] | [A] , [u] = {!!} , {!!}
  fundamentalTerm ⊢Γ (zero x) = fundamentalℕ ⊢Γ , fundamentalZero ⊢Γ
  fundamentalTerm ⊢Γ (suc {n} t) with fundamentalTerm ⊢Γ t
  fundamentalTerm ⊢Γ (suc {n} t) | [ℕ] , [n] = [ℕ] , fundamentalSuc {n = n} ⊢Γ [ℕ] [n]
  fundamentalTerm ⊢Γ (natrec x x₁ x₂ x₃) = {!!}
  fundamentalTerm ⊢Γ (conv {t} {A} {B} ⊢t A'≡A) with fundamentalTerm ⊢Γ ⊢t | fundamentalEq ⊢Γ A'≡A
  fundamentalTerm ⊢Γ (conv {t} {A} {B} ⊢t A'≡A) | [A'] , [t] | [A']₁ , [A] , [A'≡A] =
    [A] , fundamentalConv {t} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [t]

-- Fundamental theorem for term equality

  fundamentalTermEq : ∀{Γ A t t'}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ≡ t' ∷ A → Γ ⊨⟨ ¹ ⟩t t ≡ t' ∷ A / valid ⊢Γ
  fundamentalTermEq ⊢Γ (refl D) with fundamentalTerm ⊢Γ D
  ... | [A] , [t] = modelsTermEq [A] [t] [t] λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
  fundamentalTermEq ⊢Γ (sym D) with fundamentalTermEq ⊢Γ D
  fundamentalTermEq ⊢Γ (sym D) | modelsTermEq [A] [t'] [t] [t'≡t] = modelsTermEq [A] [t] [t'] λ ⊢Δ [σ] →
      symEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t'≡t] ⊢Δ [σ])
  fundamentalTermEq ⊢Γ (trans {t} {u} {r} {A} t≡u u≡t') with fundamentalTermEq ⊢Γ t≡u | fundamentalTermEq ⊢Γ u≡t'
  fundamentalTermEq ⊢Γ (trans {t} {u} {r} {A} t≡u u≡t') | modelsTermEq [A] [t] [u] [t≡u] | modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
  modelsTermEq [A] [t]
               (proof-irrelevanceTermS {A} {r} ⊢Γ [A]₁ [A] [u]₁)
               (λ ⊢Δ [σ] → transEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
                                       (proof-irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u]₁ ⊢Δ [σ])))
  fundamentalTermEq ⊢Γ (conv {A} {B} {t} {u} t≡u A'≡A) with fundamentalTermEq ⊢Γ t≡u | fundamentalEq ⊢Γ A'≡A
  fundamentalTermEq ⊢Γ (conv {A} {B} {t} {u} t≡u A'≡A) | modelsTermEq [A'] [t] [u] [t≡u] | [A']₁ , [A] , [A'≡A] =
    modelsTermEq [A] (fundamentalConv {t} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [t])
                     (fundamentalConv {u} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [u])
                     (λ ⊢Δ [σ] → convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([A'≡A] ⊢Δ [σ])
                                             (proof-irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                                      (proj₁ ([A']₁ ⊢Δ [σ]))
                                                                      ([t≡u] ⊢Δ [σ])))
  fundamentalTermEq ⊢Γ (Π-cong x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (app-cong x x₁) = {!!}
  fundamentalTermEq ⊢Γ (β-red x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (fun-ext x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (suc-cong x) with fundamentalTermEq ⊢Γ x
  fundamentalTermEq ⊢Γ (suc-cong {t} {u} x) | modelsTermEq [A] [t] [u] [t≡u] =
    modelsTermEq [A] (fundamentalSuc {n = t} ⊢Γ [A] [t])
                     (fundamentalSuc {n = u} ⊢Γ [A] [u])
                     (λ ⊢Δ [σ] → sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq ⊢Γ (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'} F≡F' z≡z' s≡s' n≡n')
    with fundamentalEq (⊢Γ ∙ ℕ ⊢Γ) F≡F' |
         fundamentalTermEq ⊢Γ z≡z'      |
         fundamentalTermEq ⊢Γ s≡s'      |
         fundamentalTermEq ⊢Γ n≡n'
  fundamentalTermEq ⊢Γ (natrec-cong {z} {z'} {s} {s'} {n} {n'} {F} {F'} F≡F' z≡z' s≡s' n≡n') |
    [F] , [F'] , [F≡F'] |
    modelsTermEq [F₀] [z] [z'] [z≡z'] |
    modelsTermEq [F₊] [s] [s'] [s≡s'] |
    modelsTermEq [ℕ] [n] [n'] [n≡n'] =
    modelsTermEq (substS {ℕ} {F} {n} ⊢Γ (ℕ ⊢Γ) [ℕ] [F] [n])
                 (fundamentalNatrec {F} {z} {s} {n} ⊢Γ [ℕ] [F] [F₀] [F₊] {!!} [z] [s] [n])
                 {!fundamentalNatrec {F'} {z'} {s'} {n'} ⊢Γ [ℕ] [F'] {![F₀]!} {![F₊]!} {!!} [z'] [s'] [n']!}
                 (λ ⊢Δ [σ] → {!!})
  fundamentalTermEq ⊢Γ (natrec-zero F z s) with fundamental (⊢Γ ∙ ℕ ⊢Γ) F | fundamentalTerm ⊢Γ z | fundamentalTerm ⊢Γ s
  fundamentalTermEq ⊢Γ (natrec-zero F z s) | [F] | [F₀] , [z] | [s] = modelsTermEq [F₀] {!!} [z] {!!}
  fundamentalTermEq ⊢Γ (natrec-suc n F z s) = {!!}

  fundamentalΠ : ∀ {F G Γ} (⊢Γ : ⊢ Γ) ([F] : Γ ⊨⟨ ¹ ⟩ F / valid ⊢Γ)
               → Γ ∙ F ⊨⟨ ¹ ⟩ G / valid ⊢Γ ∙ [F]
               → Γ ⊨⟨ ¹ ⟩ Π F ▹ G / valid ⊢Γ
  fundamentalΠ ⊢Γ [F] [G] ⊢Δ [σ] =
    let ⊢F    = soundness (proj₁ ([F] ⊢Δ [σ]))
        ⊢G    = soundness (proj₁ ([G] (⊢Δ ∙ ⊢F) ({!!} , {!!})))
        ⊢ΠF▹G = Π ⊢F ▹ ⊢G
        [σF]  = proj₁ ([F] ⊢Δ [σ])
        [σG]  = proj₁ ([G] (⊢Δ ∙ ⊢F) {!!})
    in  Π (idRed:*: ⊢ΠF▹G) ⊢F ⊢G (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF]) (λ ρ ⊢Δ₁ x → {!!}) (λ ρ ⊢Δ₁ [a] x → {!!})
    ,   (λ x → Π¹[ _ , _ , id {!⊢ΠF▹G!} , {!!} , (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] {!!}) , (λ ρ ⊢Δ₁ [a] → {!!}) ])

  substS : ∀ {F G t Γ} (⊢Γ : ⊢ Γ) (⊢F : Γ ⊢ F)
           ([F] : Γ ⊨⟨ ¹ ⟩ F / valid ⊢Γ)
           ([G] : Γ ∙ F ⊨⟨ ¹ ⟩ G / valid (⊢Γ ∙ ⊢F))
           ([t] : Γ ⊨⟨ ¹ ⟩t t ∷ F / valid ⊢Γ / [F])
         → Γ ⊨⟨ ¹ ⟩ G [ t ] / valid ⊢Γ
  substS ⊢Γ ⊢F [F] [G] [t] ⊢Δ [σ] = {!!} , (λ x → {!!})

  subst↑S : ∀ {F G t Γ} (⊢Γ : ⊢ Γ)
            ([F] : Γ ⊨⟨ ¹ ⟩ F / valid ⊢Γ)
            ([G] : Γ ∙ F ⊨⟨ ¹ ⟩ G / valid ⊢Γ ∙ [F])
            ([t] : Γ ⊨⟨ ¹ ⟩t t ∷ F / valid ⊢Γ / [F])
          → Γ ∙ F ⊨⟨ ¹ ⟩ G [ t ]↑ / valid ⊢Γ ∙ [F]
  subst↑S ⊢Γ [F] [G] [t] ⊢Δ [σ] = {!!}

  fundamentalNatrec : ∀ {F z s n Γ} (⊢Γ : ⊢ Γ)
                      ([ℕ]  : Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ)
                      ([F]  : Γ ∙ ℕ ⊨⟨ ¹ ⟩ F / valid (⊢Γ ∙ ℕ ⊢Γ))
                      ([F₀] : Γ ⊨⟨ ¹ ⟩ F [ zero ] / valid ⊢Γ)
                      ([F₊] : Γ ⊨⟨ ¹ ⟩ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / valid ⊢Γ)
                      ([Fₙ] : Γ ⊨⟨ ¹ ⟩ F [ n ] / valid ⊢Γ)
                    → Γ ⊨⟨ ¹ ⟩t z ∷ F [ zero ] / valid ⊢Γ / [F₀]
                    → Γ ⊨⟨ ¹ ⟩t s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑) / valid ⊢Γ / [F₊]
                    → ([n] : Γ ⊨⟨ ¹ ⟩t n ∷ ℕ / valid ⊢Γ / [ℕ])
                    → Γ ⊨⟨ ¹ ⟩t natrec F z s n ∷ F [ n ] / valid ⊢Γ / substS {ℕ} {F} {n} ⊢Γ (ℕ ⊢Γ) [ℕ] [F] [n]
  fundamentalNatrec = {!!}
