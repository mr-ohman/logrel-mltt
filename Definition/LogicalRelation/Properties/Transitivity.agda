module Definition.LogicalRelation.Properties.Transitivity where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  transEqT : ∀ {Γ A B C l l' l''}
             {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B} {[C] : Γ ⊩⟨ l'' ⟩ C}
           → Tactic Γ l  l'  A B [A] [B]
           → Tactic Γ l' l'' B C [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l' ⟩ B ≡ C / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEqT (ℕ D D') (ℕ _ D'') A≡B B≡C = B≡C
  transEqT (ne (ne K D neK) (ne K₁ D₁ neK₁)) (ne ._ (ne K₂ D₂ neK₂))
           (ne₌ M D' neM K≡M) (ne₌ M₁ D'' neM₁ K≡M₁) =
    ne₌ M₁  D''  neM₁
        (trans K≡M (trans (trans (sym (subset* (red D')))
                                 (subset* (red D₁)))
                           K≡M₁))
  transEqT {Γ} {l = l} {l' = l′} {l'' = l″}
           (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)
              (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
           (Π ._ (Π F₂ G₂ D₂ ⊢F₂ ⊢G₂ [F]₂ [G]₂ G-ext₂))
           (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (Π₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let F₁≡F′  , G₁≡G′  = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D′  , Π))
        F₂≡F″ , G₂≡G″ = Π-PE-injectivity (whrDet*' (red D₂ , Π) (D″ , Π))
        substLift {Δ} {l} {a} ρ x = Δ ⊩⟨ l ⟩ U.wk (lift ρ) x [ a ]
        [F′] : ∀ {Δ} ρ ⊢Δ → Δ ⊩⟨ l′ ⟩ wkₜ ρ F′
        [F′] ρ ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₁≡F′ ([F]₁ ρ ⊢Δ)
        [F″] : ∀ {Δ} ρ ⊢Δ → Δ ⊩⟨ l″ ⟩ wkₜ ρ F″
        [F″] ρ ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wkₜ ρ x) F₂≡F″ ([F]₂ ρ ⊢Δ)
        [F′≡F″] : ∀ {Δ} ρ ⊢Δ → Δ ⊩⟨ l′ ⟩ wkₜ ρ F′ ≡ wkₜ ρ F″ / [F′] ρ ⊢Δ
        [F′≡F″] ρ ⊢Δ = irrelevanceEq' (PE.cong (wkₜ ρ) F₁≡F′)
                                      ([F]₁ ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′]₁ ρ ⊢Δ)
        [G′] : ∀ {Δ a} ρ ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ wkₜ ρ F′ / [F′] ρ ⊢Δ
             → Δ ⊩⟨ l′ ⟩ wkLiftₜ ρ G′ [ a ]
        [G′] ρ ⊢Δ [a] =
          let [a′] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₁≡F′))
                                      ([F′] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [a]
          in  PE.subst (substLift (toWk ρ)) G₁≡G′ ([G]₁ ρ ⊢Δ [a′])
        [G″] : ∀ {Δ a} ρ ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ wkₜ ρ F″ / [F″] ρ ⊢Δ
             → Δ ⊩⟨ l″ ⟩ wkLiftₜ ρ G″ [ a ]
        [G″] ρ ⊢Δ [a] =
          let [a″] = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₂≡F″))
                                      ([F″] ρ ⊢Δ) ([F]₂ ρ ⊢Δ) [a]
          in  PE.subst (substLift (toWk ρ)) G₂≡G″ ([G]₂ ρ ⊢Δ [a″])
        [G′≡G″] : ∀ {Δ a} ρ ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ wkₜ ρ F′ / [F′] ρ ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ wkLiftₜ ρ G′  [ a ]
                          ≡ wkLiftₜ ρ G″ [ a ] / [G′] ρ ⊢Δ [a]
        [G′≡G″] ρ ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm' (PE.cong (wkₜ ρ) (PE.sym F₁≡F′))
                                      ([F′] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) [a′]
          in  irrelevanceEq' (PE.cong (λ x → wkLiftₜ ρ x [ _ ]) G₁≡G′)
                             ([G]₁ ρ ⊢Δ [a]₁) ([G′] ρ ⊢Δ [a′])
                             ([G≡G′]₁ ρ ⊢Δ [a]₁)
    in  Π₌ F″ G″ D″ (trans A≡B A≡B₁)
           (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
                             ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
           (λ ρ ⊢Δ [a] →
              let [a′] = convTerm₁ ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                  [a″] = convTerm₁ ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
              in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                          ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′]))
  transEqT (U ⊢Γ ⊢Γ₁) (U .⊢Γ₁ ⊢Γ₂) A≡B B≡C = A≡B
  transEqT (emb⁰¹ AB) BC A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT (emb¹⁰ AB) (emb⁰¹ BC) A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT (emb¹⁰ AB) (emb¹⁰ (emb⁰¹ BC)) A≡B B≡C = transEqT AB BC A≡B B≡C
  transEqT AB (emb¹⁰ BC) A≡B B≡C = transEqT AB BC A≡B B≡C

  transEq : ∀ {Γ A B C l l' l''}
            ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) ([C] : Γ ⊩⟨ l'' ⟩ C)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l' ⟩ B ≡ C / [B]
          → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEq [A] [B] [C] A≡B B≡C =
    transEqT (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C) A≡B B≡C

  transEq' : ∀ {Γ A B B' C C' l l' l''} → B PE.≡ B' → C PE.≡ C'
           → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) ([C] : Γ ⊩⟨ l'' ⟩ C)
           → Γ ⊩⟨ l ⟩  A ≡ B' / [A]
           → Γ ⊩⟨ l' ⟩ B ≡ C' / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C  / [A]
  transEq' PE.refl PE.refl [A] [B] [C] A≡B B≡C = transEq [A] [B] [C] A≡B B≡C

mutual
  transEqTermℕ : ∀ {Γ n n' n''}
               → Γ ⊩ℕ n  ≡ n'  ∷ℕ
               → Γ ⊩ℕ n' ≡ n'' ∷ℕ
               → Γ ⊩ℕ n  ≡ n'' ∷ℕ
  transEqTermℕ (ℕₜ₌ k k' d d' t≡u prop)
               (ℕₜ₌ k₁ k'' d₁ d'' t≡u₁ prop₁) =
    let k₁Whnf = naturalWhnf (proj₁ (split prop₁))
        k'Whnf = naturalWhnf (proj₂ (split prop))
        k₁≡k' = whrDet* (redₜ d₁ , k₁Whnf) (redₜ d' , k'Whnf)
        prop' = PE.subst (λ x → [Natural]-prop _ x _) k₁≡k' prop₁
    in  ℕₜ₌ k k'' d d'' (trans t≡u t≡u₁)
            (transNatural-prop prop prop')

  transNatural-prop : ∀ {Γ k k' k''}
                    → [Natural]-prop Γ k k'
                    → [Natural]-prop Γ k' k''
                    → [Natural]-prop Γ k k''
  transNatural-prop (suc x) (suc x₁) = suc (transEqTermℕ x x₁)
  transNatural-prop (suc x) (ne () x₂ x₃)
  transNatural-prop zero prop₁ = prop₁
  transNatural-prop prop zero = prop
  transNatural-prop (ne x () x₂) (suc x₃)
  transNatural-prop (ne x x₁ x₂) (ne x₃ x₄ x₅) = ne x x₄ (trans x₂ x₅)

transEqTerm : ∀ {l Γ A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]
transEqTerm (U' .⁰ 0<1 ⊢Γ)
            (Uₜ₌ ⊢t ⊢u t≡u ⊩t ⊩u [t≡u])
            (Uₜ₌ ⊢t₁ ⊢u₁ t≡u₁ ⊩t₁ ⊩u₁ [t≡u]₁) =
  Uₜ₌ ⊢t ⊢u₁ (trans t≡u t≡u₁) ⊩t ⊩u₁
      (transEq ⊩t ⊩u ⊩u₁ [t≡u] (irrelevanceEq ⊩t₁ ⊩u [t≡u]₁))
transEqTerm (ℕ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
transEqTerm (ne' _ _ _) t≡u u≡v = trans t≡u u≡v
transEqTerm (Π' F G D ⊢F ⊢G [F] [G] G-ext)
            (t≡u , ⊩t , ⊩u , [t≡u])
            (t≡u₁ , ⊩t₁ , ⊩u₁ , [t≡u]₁) =
  trans t≡u t≡u₁ , ⊩t , ⊩u₁
    , (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
                                ([t≡u] ρ ⊢Δ [a])
                                ([t≡u]₁ ρ ⊢Δ [a]))
transEqTerm (emb 0<1 x) t≡u u≡v = transEqTerm x t≡u u≡v
