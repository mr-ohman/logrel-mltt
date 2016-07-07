module Definition.LogicalRelation.Properties.Transitivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Data.Product
import Relation.Binary.PropositionalEquality as PE


mutual
  transEqT : ∀ {Γ A B C l l' l''} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B} {[C] : Γ ⊩⟨ l'' ⟩ C}
           → Tactic Γ l l' A B [A] [B] → Tactic Γ l' l'' B C [B] [C]
           → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ C / [B] → Γ ⊩⟨ l ⟩ A ≡ C / [A]
  transEqT (ℕ D D₁) (ℕ .D₁ D₂) A≡B B≡C = B≡C
  transEqT (ne D neK D₁ neK₁) (ne .D₁ .neK₁ D₂ neK₂) ne[ M , D' , neM , K≡M ] ne[ M₁ , D'' , neM₁ , K≡M₁ ] = ne[ M₁ , D'' , neM₁ , trans K≡M (trans (trans (sym (subset* (red D'))) (subset* (red D₁))) K≡M₁) ]
  transEqT {Γ} {l = l} {l' = l'} {l'' = l''}
           (Π D ⊢F ⊢G [F] [G] G-ext D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)
           (Π .D₁ .⊢F₁ .⊢G₁ .[F]₁ .[G]₁ .G-ext₁ D₂ ⊢F₂ ⊢G₂ [F]₂ [G]₂ G-ext₂)
           Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ]
           Π¹[ F'' , G'' , D'' , A≡B₁ , [F≡F']₁ , [G≡G']₁ ] =
    let F₁≡F'  , G₁≡G'  = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D'  , Π))
        F₂≡F'' , G₂≡G'' = Π-PE-injectivity (whrDet*' (red D₂ , Π) (D'' , Π))
        [F'] : ∀ {Δ} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l' ⟩ wkₜ ρ F'
        [F'] ρ ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F' ([F]₁ ρ ⊢Δ)
        [F''] : ∀ {Δ} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l'' ⟩ wkₜ ρ F''
        [F''] ρ ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₂≡F'' ([F]₂ ρ ⊢Δ)
        [F'≡F''] : ∀ {Δ} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l' ⟩ wkₜ ρ F' ≡ wkₜ ρ F'' / [F'] ρ ⊢Δ
        [F'≡F''] ρ ⊢Δ = irrelevanceEq' (PE.cong (wkₜ ρ) F₁≡F') ([F]₁ ρ ⊢Δ) ([F'] ρ ⊢Δ) ([F≡F']₁ ρ ⊢Δ)
        [G'] : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l' ⟩ a ∷ wkₜ ρ F' / [F'] ρ ⊢Δ → Δ ⊩⟨ l' ⟩ wkLiftₜ ρ G' [ a ]
        [G'] ρ ⊢Δ [a] = let [a'] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F'] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [a]
                        in  PE.subst (λ x →  _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₁≡G' ([G]₁ ρ ⊢Δ [a'])
        [G''] : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l'' ⟩ a ∷ wkₜ ρ F'' / [F''] ρ ⊢Δ → Δ ⊩⟨ l'' ⟩ wkLiftₜ ρ G'' [ a ]
        [G''] ρ ⊢Δ [a] = let [a''] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₂≡F'')) ([F''] ρ ⊢Δ) ([F]₂ ρ ⊢Δ) [a]
                        in  PE.subst (λ x →  _ ⊩⟨ _ ⟩ wkLiftₜ ρ x [ _ ]) G₂≡G'' ([G]₂ ρ ⊢Δ [a''])
        [G'≡G''] : ∀ {Δ a} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⟨ l' ⟩ a ∷ wkₜ ρ F' / [F'] ρ ⊢Δ) → Δ ⊩⟨ l' ⟩ wkLiftₜ ρ G' [ a ] ≡ wkLiftₜ ρ G'' [ a ] / [G'] ρ ⊢Δ [a]
        [G'≡G''] ρ ⊢Δ [a'] = let [a]₁ = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₁≡F')) ([F'] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [a']
                             in  irrelevanceEq' (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) G₁≡G') ([G]₁ ρ ⊢Δ [a]₁) ([G'] ρ ⊢Δ [a']) ([G≡G']₁ ρ ⊢Δ [a]₁)
    in  Π¹[ F'' , G'' , D'' , trans A≡B A≡B₁
        , (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F'] ρ ⊢Δ) ([F''] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ) ([F'≡F''] ρ ⊢Δ))
        , (λ ρ ⊢Δ [a] → let [a']  = convTerm₁ ([F] ρ ⊢Δ) ([F'] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ) [a]
                            [a''] = convTerm₁ ([F'] ρ ⊢Δ) ([F''] ρ ⊢Δ) ([F'≡F''] ρ ⊢Δ) [a']
                        in  transEq ([G] ρ ⊢Δ [a]) ([G'] ρ ⊢Δ [a']) ([G''] ρ ⊢Δ [a'']) ([G≡G'] ρ ⊢Δ [a]) ([G'≡G''] ρ ⊢Δ [a'])) ]
  transEqT (U ⊢Γ ⊢Γ₁) (U .⊢Γ₁ ⊢Γ₂) A≡B B≡C = PE.refl
  transEqT (emb⁰¹ AB) BC A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT (emb¹⁰ AB) (emb⁰¹ BC) A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT (emb¹⁰ AB) (emb¹⁰ (emb⁰¹ BC)) A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT AB (emb¹⁰ BC) A≡B B≡C = transEqT AB BC A≡B B≡C

  transEq : ∀ {Γ A B C l l' l''} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) ([C] : Γ ⊩⟨ l'' ⟩ C)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ C / [B] → Γ ⊩⟨ l ⟩ A ≡ C / [A]
  transEq [A] [B] [C] A≡B B≡C = transEqT (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C) A≡B B≡C


transNatural : ∀ {Γ n n' n''}
             → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n  n'
             → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n' n''
             → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n  n''
transNatural (suc a) (suc b) = suc (trans a b)
transNatural (suc a) (ne () x₁ x₂)
transNatural zero b = b
transNatural (ne x () x₂) (suc b)
transNatural (ne x x₁ x₂) zero = ne x x₁ x₂
transNatural (ne x x₁ x₂) (ne x₃ x₄ x₅) = ne x x₄ (trans x₂ x₅)

transEqTerm : ∀ {l Γ A t u v} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A] → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]
transEqTerm {⁰} (U {l< = ()} ⊢Γ) t≡u u≡v
transEqTerm {¹} (U {l< = 0<1} ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] U[ ⊢t₁ , ⊢u₁ , t≡u₁ , ⊩t₁ , ⊩u₁ , [t≡u]₁ ] = U[ ⊢t , ⊢u₁ , trans t≡u t≡u₁ , ⊩t , ⊩u₁ , transEq ⊩t ⊩u ⊩u₁ [t≡u] (irrelevanceEq ⊩t₁ ⊩u [t≡u]₁) ]
transEqTerm (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] ℕ≡[ k₁ , k'' , d₁ , d'' , t≡u₁ , [k≡k']₁ ] =
  let k₁Whnf = naturalWhnf (proj₁ (split [k≡k']₁))
      k'Whnf = naturalWhnf (proj₂ (split [k≡k']))
      k₁≡k' = whrDet* (redₜ d₁ , k₁Whnf) (redₜ d' , k'Whnf)
      [k'≡k''] = PE.subst (λ x → [Natural] _ x _) k₁≡k' [k≡k']₁
  in  ℕ≡[ k , k'' , d , d'' , trans t≡u t≡u₁ , transNatural [k≡k'] [k'≡k''] ]
transEqTerm (ne D neK) t≡u u≡v = trans t≡u u≡v
transEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) (t≡u , ⊩t , ⊩u , [t≡u]) (t≡u₁ , ⊩t₁ , ⊩u₁ , [t≡u]₁) = trans t≡u t≡u₁ , ⊩t , ⊩u₁ , (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a]) ([t≡u] ρ ⊢Δ [a]) ([t≡u]₁ ρ ⊢Δ [a]))
transEqTerm {⁰} (emb {l< = ()} x) t≡u u≡v
transEqTerm {¹} (emb {l< = 0<1} x) t≡u u≡v = transEqTerm x t≡u u≡v
