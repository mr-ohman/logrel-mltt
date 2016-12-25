{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

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
  symEqT : ∀ {Γ A B l l'} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
         → Tactic Γ l l' A B [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B / [A]
         → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEqT (ℕ D D') A≡B = red D
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D' neM K≡M)
         rewrite whrDet*' (red D' , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK
        (≅-sym K≡M) --(trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)))
  symEqT (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F' G' D' A≡B [F≡F'] [G≡G']) =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF'≡ρF₁ ρ = PE.cong (U.wk ρ) (PE.sym F₁≡F')
              [ρF'] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ U.wk ρ x) F₁≡F' ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq' {Δ} (ρF'≡ρF₁ ρ)
                             ([ρF'] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq ([F] [ρ] ⊢Δ) ([ρF'] [ρ] ⊢Δ)
                                    ([F≡F'] [ρ] ⊢Δ))
    in  Π₌ _ _ (red D) (≅-sym A≡B)
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG'a≡ρG₁'a = PE.cong (λ x → U.wk (lift ρ) x [ _ ]) (PE.sym G₁≡G')
                   [ρG'a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ U.wk (lift ρ) x [ _ ]) G₁≡G'
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq' ρG'a≡ρG₁'a
                                  [ρG'a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG'a]
                                         ([G≡G'] [ρ] ⊢Δ [a]₁)))
  symEqT (U (U _ _ _) (U _ _ _)) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  symEq : ∀ {Γ A B l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
        → Γ ⊩⟨ l ⟩ A ≡ B / [A]
        → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNeutralTerm : ∀ {t u A Γ}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (≅ₜ-sym k≡m)

symNatural-prop : ∀ {Γ k k'}
                → [Natural]-prop Γ k k'
                → [Natural]-prop Γ k' k
symNatural-prop (suc (ℕₜ₌ k k' d d' t≡u prop)) =
  suc (ℕₜ₌ k' k d' d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zero = zero
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (U' .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d' typeA typeB A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A d' d typeB typeA (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕ D) (ℕₜ₌ k k' d d' t≡u prop) =
  ℕₜ₌ k' k d' d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm (ne' K D neK K≡K) (neₜ₌ k m d d' nf) = neₜ₌ m k d' d (symNeutralTerm nf)
symEqTerm (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d' funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d' d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
