module Lemma.Fundamental where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty

import Relation.Binary.PropositionalEquality as PE


-- TODO: Move to Properties
sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ) → Γ ⊩⟨ l ⟩ n ∷ ℕ / [ℕ] → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / [ℕ]
sucTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] = ℕ[ _ , [ suc ⊢t , suc ⊢t , id (suc ⊢t) ] , suc , ⊢t ]
sucTerm (ne D neK) [n] = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
sucTerm (Π D ⊢F ⊢G [F] [G] G-ext) [n] = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
sucTerm (emb {l< = 0<1} x) [n] = sucTerm x [n]

sucEqTerm : ∀ {l Γ n n'} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ) → Γ ⊩⟨ l ⟩ n ≡ n' ∷ ℕ / [ℕ] → Γ ⊩⟨ l ⟩ suc n ≡ suc n' ∷ ℕ / [ℕ]
sucEqTerm (ℕ D) ℕ≡[ k , k' , [ ⊢t , ⊢u , d ] , [ ⊢t₁ , ⊢u₁ , d₁ ] , t≡u , [k≡k'] ] = ℕ≡[ _ , _ , idRedTerm:*: (suc ⊢t) , idRedTerm:*: (suc ⊢t₁) , suc-cong t≡u , suc t≡u ]
sucEqTerm (ne D neK) [n≡n'] = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
sucEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) [n≡n'] = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
sucEqTerm (emb {l< = 0<1} x) [n≡n'] = sucEqTerm x [n≡n']


mutual
  valid : ∀ {Γ} → ⊢ Γ → ⊨⟨ ¹ ⟩ Γ
  valid ε = ε
  valid (⊢Γ ∙ x) = valid ⊢Γ ∙ fundamental ⊢Γ x

  fundamentalℕ : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ
  fundamentalℕ ⊢Γ ⊢Δ [σ] = ℕ (idRed:*: (ℕ ⊢Δ)) , λ x₂ → id (ℕ ⊢Δ)

  fundamentalU : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊨⟨ ¹ ⟩ U / valid ⊢Γ
  fundamentalU ⊢Γ ⊢Δ [σ] = U {l< = 0<1} ⊢Δ , λ x₂ → PE.refl

  fundamentalSuc : ∀ {Γ n} (⊢Γ : ⊢ Γ) ([ℕ] : Γ ⊨⟨ ¹ ⟩ ℕ / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t n ∷ ℕ / valid ⊢Γ / [ℕ] → Γ ⊨⟨ ¹ ⟩t suc n ∷ ℕ / valid ⊢Γ / [ℕ]
  fundamentalSuc ⊢Γ [ℕ] [n] = λ ⊢Δ [σ] → sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ])) , (λ x → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x))

  fundamentalConv : ∀ {t A B Γ} (⊢Γ : ⊢ Γ) ([A] [A'] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A'] → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A] → Γ ⊨⟨ ¹ ⟩t t ∷ B / valid ⊢Γ / [B]
  fundamentalConv ⊢Γ [A] [A'] [B] [A≡B] [t] ⊢Δ [σ] =
    let [σA]     = proj₁ ([A] ⊢Δ [σ])
        [σA']    = proj₁ ([A'] ⊢Δ [σ])
        [σB]     = proj₁ ([B] ⊢Δ [σ])
        [σA≡σB]  = proof-irrelevanceEq [σA'] [σA] ([A≡B] ⊢Δ [σ])
        [σt]     = proj₁ ([t] ⊢Δ [σ])
        [σt≡σ't] = proj₂ ([t] ⊢Δ [σ])
    in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
    ,   λ [σ≡σ'] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ't] [σ≡σ'])

  fundamental : ∀ {Γ A} (⊢Γ : ⊢ Γ) (⊢A : Γ ⊢ A) → Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ
  fundamental ⊢Γ (ℕ x) = fundamentalℕ ⊢Γ
  fundamental ⊢Γ (U x) = fundamentalU ⊢Γ
  fundamental ⊢Γ (Π F ▹ G) ⊢Δ [σ] with fundamental ⊢Γ F | fundamental (⊢Γ ∙ F) G
  ... | [F] | [G] = {!!}
  fundamental ⊢Γ (univ x) ⊢Δ [σ] with fundamentalTerm ⊢Γ x
  fundamental ⊢Γ (univ x) ⊢Δ [σ] | [U] , [A] =
    let [A]₁ = emb {l< = 0<1} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
    in [A]₁ , (λ x₁ → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁ ((proj₂ ([A] ⊢Δ [σ])) x₁))

  fundamentalEq : ∀{Γ A B}  (⊢Γ : ⊢ Γ) → Γ ⊢ A ≡ B
    → ∃₂ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) ([B] : Γ ⊨⟨ ¹ ⟩ B / valid ⊢Γ)
    → Γ ⊨⟨ ¹ ⟩ A ≡ B / valid ⊢Γ / [A]
  fundamentalEq ⊢Γ (univ x) with fundamentalTermEq ⊢Γ x
  fundamentalEq ⊢Γ (univ x) | modelsTermEq [A] [t] [u] [t≡u] = {!!} , {!!} , {!!}
  fundamentalEq ⊢Γ (refl D) = let [B] = fundamental ⊢Γ D
                              in  [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (sym A≡B) with fundamentalEq ⊢Γ A≡B
  fundamentalEq ⊢Γ (sym A≡B) | [B] , [A] , [B≡A] = [A] , [B]
                                                 , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([B≡A] ⊢Δ [σ]))
  fundamentalEq ⊢Γ (trans A≡B₁ B₁≡B) with fundamentalEq ⊢Γ A≡B₁ | fundamentalEq ⊢Γ B₁≡B
  fundamentalEq ⊢Γ (trans A≡B B≡C) | [A] , [B₁] , [A≡B₁] | [B₁]₁ , [B] , [B₁≡B] =
    [A] , [B] , (λ ⊢Δ [σ] → transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) ([A≡B₁] ⊢Δ [σ]) (proof-irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ])) ([B₁≡B] ⊢Δ [σ])))
  fundamentalEq ⊢Γ (Π-cong x A≡B A≡B₁) with fundamentalEq ⊢Γ A≡B | fundamentalEq (⊢Γ ∙ x) A≡B₁
  fundamentalEq ⊢Γ (Π-cong x A≡B A≡B₁) | [F] , [H] , [F≡H] | [G] , [E] , [G≡E] =
    {!!} , {!!} , {!!}

  fundamentalTerm : ∀{Γ A t}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ∷ A →
    ∃ λ ([A] : Γ ⊨⟨ ¹ ⟩ A / valid ⊢Γ) → Γ ⊨⟨ ¹ ⟩t t ∷ A / valid ⊢Γ / [A]
  fundamentalTerm ⊢Γ (ℕ x) = fundamentalU ⊢Γ
                           , (λ ⊢Δ [σ] → let ⊢ℕ  = ℕ ⊢Δ
                                             [ℕ] = ℕ (idRed:*: (ℕ ⊢Δ))
                                         in  (⊢ℕ , [ℕ]) , (λ x₁ → U[ ⊢ℕ , ⊢ℕ , refl ⊢ℕ , [ℕ] , [ℕ] , id (ℕ ⊢Δ) ]))
  fundamentalTerm ⊢Γ (Π x ▹ x₁) = fundamentalU ⊢Γ , {!!}
  fundamentalTerm ⊢Γ (var x₁ x₂) = {!!}
  fundamentalTerm ⊢Γ (lam x x₁) = {!!}
  fundamentalTerm ⊢Γ (Dt ∘ Du) with fundamentalTerm ⊢Γ Dt | fundamentalTerm ⊢Γ Du
  ... | [ΠAB] , [t] | [A] , [u] = (λ ⊢Δ [σ] → {!!} , {!!}) , {!!}
  fundamentalTerm ⊢Γ (zero x) = fundamentalℕ ⊢Γ , (λ ⊢Δ [σ] → ℕ[ zero , idRedTerm:*: (zero ⊢Δ) , zero , tt ] , (λ x₁ → ℕ≡[ zero , zero , idRedTerm:*: (zero ⊢Δ) , idRedTerm:*: (zero ⊢Δ) , refl (zero ⊢Δ) , zero ]))
  fundamentalTerm ⊢Γ (suc {n} t) with fundamentalTerm ⊢Γ t
  fundamentalTerm ⊢Γ (suc {n} t) | [ℕ] , [n] = [ℕ] , fundamentalSuc {n = n} ⊢Γ [ℕ] [n]
  fundamentalTerm ⊢Γ (natrec x x₁ x₂ x₃) = {!!}
  fundamentalTerm ⊢Γ (conv {t} {A} {B} ⊢t A'≡A) with fundamentalTerm ⊢Γ ⊢t | fundamentalEq ⊢Γ A'≡A
  fundamentalTerm ⊢Γ (conv {t} {A} {B} ⊢t A'≡A) | [A'] , [t] | [A']₁ , [A] , [A'≡A] =
    [A] , fundamentalConv {t} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [t]

  fundamentalTermEq : ∀{Γ A t t'}  (⊢Γ : ⊢ Γ) → Γ ⊢ t ≡ t' ∷ A → Γ ⊨⟨ ¹ ⟩t t ≡ t' ∷ A / valid ⊢Γ
  fundamentalTermEq ⊢Γ (refl D) with fundamentalTerm ⊢Γ D
  ... | [A] , [t] = modelsTermEq [A] [t] [t] λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
  fundamentalTermEq ⊢Γ (sym D) with fundamentalTermEq ⊢Γ D
  fundamentalTermEq ⊢Γ (sym D) | modelsTermEq [A] [t'] [t] [t'≡t] = modelsTermEq [A] [t] [t'] λ ⊢Δ [σ] →
      symEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t'≡t] ⊢Δ [σ])
  fundamentalTermEq ⊢Γ (trans t≡u u≡t') with fundamentalTermEq ⊢Γ t≡u | fundamentalTermEq ⊢Γ u≡t'
  fundamentalTermEq ⊢Γ (trans t≡u u≡t') | modelsTermEq [A] [t] [u] [t≡u] | modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ = modelsTermEq [A] [t] {![u]₁!} (λ ⊢Δ [σ] → transEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]) (proof-irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u]₁ ⊢Δ [σ])))
  fundamentalTermEq ⊢Γ (conv {A} {B} {t} {u} t≡u A'≡A) with fundamentalTermEq ⊢Γ t≡u | fundamentalEq ⊢Γ A'≡A
  fundamentalTermEq ⊢Γ (conv {A} {B} {t} {u} t≡u A'≡A) | modelsTermEq [A'] [t] [u] [t≡u] | [A']₁ , [A] , [A'≡A] =
    modelsTermEq [A] (fundamentalConv {t} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [t]) (fundamentalConv {u} {A} {B} ⊢Γ [A'] [A']₁ [A] [A'≡A] [u])
                 (λ ⊢Δ [σ] → convEqTerm₁ (proj₁ ([A']₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([A'≡A] ⊢Δ [σ])
                                         (proof-irrelevanceEqTerm (proj₁ ([A'] ⊢Δ [σ]))
                                                                  (proj₁ ([A']₁ ⊢Δ [σ]))
                                                                  ([t≡u] ⊢Δ [σ])))
  fundamentalTermEq ⊢Γ (Π-cong x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (app-cong x x₁) = {!!}
  fundamentalTermEq ⊢Γ (β-red x x₁ x₂) = {!!}
  fundamentalTermEq ⊢Γ (fun-ext x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (suc-cong x) with fundamentalTermEq ⊢Γ x
  fundamentalTermEq ⊢Γ (suc-cong {t} {u} x) | modelsTermEq [A] [t] [u] [t≡u] = modelsTermEq [A] (fundamentalSuc {n = t} ⊢Γ [A] [t]) (fundamentalSuc {n = u} ⊢Γ [A] [u]) (λ ⊢Δ [σ] → sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq ⊢Γ (natrec-cong x x₁ x₂ x₃) = {!!}
  fundamentalTermEq ⊢Γ (natrec-zero F z s) with fundamental (⊢Γ ∙ ℕ ⊢Γ) F | fundamentalTerm ⊢Γ z | fundamentalTerm ⊢Γ s
  fundamentalTermEq ⊢Γ (natrec-zero F₁ z s₁) | [F] | [F₀] , [z] | [s] = modelsTermEq [F₀] {!!} [z] {!!}
  fundamentalTermEq ⊢Γ (natrec-suc x x₁ x₂ x₃) = {!!}
