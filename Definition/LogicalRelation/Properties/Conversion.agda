{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Conversion {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Wellformed

open import Tools.Product
import Tools.PropositionalEquality as PE


convRed:*: : ∀ {t u A B Γ} → Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t :⇒*: u ∷ B
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]

mutual
  convTermT₁ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
             → Tactic Γ l l' A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l ⟩  t ∷ A / [A]
             → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
  convTermT₁ (ℕ D D') A≡B t = t
  convTermT₁ {l} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) A≡B
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let A≅B = wellformedEq {l} (ne' K D neK K≡K) A≡B
    in  neₜ k (convRed:*: d (≅-eq A≅B))
            (neNfₜ neK₂ (conv ⊢k (≅-eq A≅B)) (≅-conv k≡k A≅B))
  convTermT₁ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F' G' D' A≡B [F≡F'] [G≡G'])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
    in  Πₜ f (convRed:*: d (≅-eq A≡B)) funcF (≅-conv f≡f A≡B)
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
                        -- TODO Add new irrelevance function for these cases,
                        --      since only the second part is relevant here.
              let [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                           ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G'))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G'] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
          (λ {ρ} [ρ] ⊢Δ [a] →
             let [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                          ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                   (PE.sym G₁≡G'))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G'] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₁ (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t

  convTermT₂ : ∀ {l l' Γ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
           → Tactic Γ l l' A B [A] [B]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
           → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTermT₂ (ℕ D D') A≡B t = t
  convTermT₂ {l} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) A≡B
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let B≅A = ≅-sym (wellformedEq {l} (ne' K D neK K≡K) A≡B)
    in  neₜ k (convRed:*: d (≅-eq B≅A))
            (neNfₜ neK₂ (conv ⊢k (≅-eq B≅A)) (≅-conv k≡k B≅A))
  convTermT₂ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F' G' D' A≡B [F≡F'] [G≡G'])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
    in  Πₜ f (convRed:*: d (sym (≅-eq A≡B))) funcF (≅-conv f≡f (≅-sym A≡B))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                           ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G'))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G'] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                           ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G'))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G'] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₂ (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t

  convTerm₁ : ∀ {Γ A B t l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A / [A]
            → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  convTerm₂ : ∀ {Γ A B t l l'} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  convTerm₂' : ∀ {Γ A B B' t l l'} → B PE.≡ B'
          → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B' / [A]
          → Γ ⊩⟨ l' ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTerm₂' PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  convEqTermT₁ : ∀ {l l' Γ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
               → Tactic Γ l l' A B [A] [B]
               → Γ ⊩⟨ l ⟩  A ≡ B / [A]
               → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
               → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕ D D') A≡B t≡u = t≡u
  convEqTermT₁ {l} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) A≡B
               (neₜ₌ k m d d' (neNfₜ₌ neK₂ neM k≡m)) =
    let A≅B = wellformedEq {l} (ne' K D neK K≡K) A≡B
        A≡B' = ≅-eq A≅B
    in  neₜ₌ k m (convRed:*: d A≡B')
                 (convRed:*: d' A≡B')
                 (neNfₜ₌ neK₂ neM (≅-conv k≡m A≅B))
  convEqTermT₁ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F' G' D' A≡B [F≡F'] [G≡G'])
               (Πₜ₌ f g d d' funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F' G' D' A≡B [F≡F'] [G≡G']
    in  Πₜ₌ f g (convRed:*: d (≅-eq A≡B)) (convRed:*: d' (≅-eq A≡B))
            funcF funcG (≅-conv t≡u A≡B)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                   [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                            ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G'))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G'] [ρ] ⊢Δ [a]₁)
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₁ (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u

  convEqTermT₂ : ∀ {l l' Γ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B}
             → Tactic Γ l l' A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕ D D') A≡B t≡u = t≡u
  convEqTermT₂ {l} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) A≡B
               (neₜ₌ k m d d' (neNfₜ₌ neK₂ neM k≡m)) =
    let B≅A = ≅-sym (wellformedEq {l} (ne' K D neK K≡K) A≡B)
        B≡A' = ≅-eq B≅A
    in  neₜ₌ k m (convRed:*: d B≡A') (convRed:*: d' B≡A')
                 (neNfₜ₌ neK₂ neM (≅-conv k≡m B≅A))
  convEqTermT₂ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F' G' D' A≡B [F≡F'] [G≡G'])
               (Πₜ₌ f g d d' funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F' G' D' A≡B [F≡F'] [G≡G']
    in  Πₜ₌ f g (convRed:*: d (sym (≅-eq A≡B))) (convRed:*: d' (sym (≅-eq A≡B)))
            funcF funcG (≅-conv t≡u (≅-sym A≡B))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F' , G₁≡G' = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D' , Π))
                   [F≡F₁] = irrelevanceEqR' (PE.cong (U.wk ρ) (PE.sym F₁≡F'))
                                            ([F] [ρ] ⊢Δ) ([F≡F'] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR' (PE.cong (λ x → U.wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G'))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G'] [ρ] ⊢Δ [a])
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂ (U (U .⁰ 0<1 ⊢Γ) (U .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u

  convEqTerm₁ : ∀ {l l' Γ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
              → Γ ⊩⟨ l ⟩  A ≡ B / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
              → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  convEqTerm₂ : ∀ {l l' Γ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l' ⟩ t ≡ u ∷ B / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u
