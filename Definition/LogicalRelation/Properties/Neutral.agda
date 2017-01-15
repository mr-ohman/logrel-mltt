open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Neutral {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Wellformed
open import Definition.LogicalRelation.Properties.Symmetry

open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE


neu : ∀ {l Γ A} (neA : Neutral A) → Γ ⊢ A → _⊩⟨_⟩_ {{eqrel}} Γ l A
neu neA A = ne (ne _ (idRed:*: A) neA (≅-nerefl A neA))

neuEq' : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neB : Neutral B)
       → Γ ⊢ A → Γ ⊢ B
       → Γ ⊢ A ≅ B
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq' (noemb (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neB A B A≡B =
  ne₌ _ (idRed:*: B) neB
      (≅-trans (≅-red (id ⊢B) D (ne neK) (ne neK) K≡K) A≡B)
neuEq' (emb 0<1 x) neB A:≡:B = neuEq' x neB A:≡:B

neuEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A → Γ ⊢ B
      → Γ ⊢ A ≅ B
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB A B A≡B =
  irrelevanceEq (ne-intr (ne-elim [A] neA))
                [A]
                (neuEq' (ne-elim [A] neA) neB A B A≡B)

mutual
  neuTerm : ∀ {l Γ A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (U' .⁰ 0<1 ⊢Γ) neN n =
    Uₜ _ (idRedTerm:*: n) (ne neN) (≅ₜ-nerefl n neN) (neu neN (univ n))
  neuTerm (ℕ [ ⊢A , ⊢B , D ]) neN n =
    let A≡ℕ = subset* D
        n≡n = ≅-conv (≅ₜ-nerefl n neN) A≡ℕ
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne neN) (neNfₜ neN (conv n A≡ℕ) n≡n)
  neuTerm (ne' K D neK K≡K) neN n =
    let A≡K = subset* (red D)
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (≅ₜ-nerefl (conv n A≡K) neN))
  neuTerm (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (≅ₜ-nerefl (conv n A≡ΠFG) neN)
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  G[a]≡G[b] = wellformedEq ([G] [ρ] ⊢Δ [b])
                                          (symEq ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [b])
                                                 (G-ext [ρ] ⊢Δ [a] [b] [a≡b]))
                  a = wellformedTerm ([F] [ρ] ⊢Δ) [a]
                  b = wellformedTerm ([F] [ρ] ⊢Δ) [b]
                  a≡b = wellformedTermEq ([F] [ρ] ⊢Δ) [a≡b]
                  ρn = conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG
                  neN∘a = _∘_ (wkNeutral ρ neN)
                  neN∘b = _∘_ (wkNeutral ρ neN)
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn ∘ a)
                            (conv (ρn ∘ b) (≅-eq G[a]≡G[b]))
                            (≅-app-cong (≅ₜ-nerefl ρn (wkNeutral ρ neN)) a≡b))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = wellformedTerm ([F] [ρ] ⊢Δ) [a]
              in  neuTerm ([G] [ρ] ⊢Δ [a]) (_∘_ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ a))
  neuTerm (emb 0<1 x) neN n = neuTerm x neN n

  neuEqTerm : ∀ {l Γ A n n'} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN' : Neutral n')
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n' ∷ A
            → Γ ⊢ n ≅ n' ∷ A
            → Γ ⊩⟨ l ⟩ n ≡ n' ∷ A / [A]
  neuEqTerm (U' .⁰ 0<1 ⊢Γ) neN neN' n n' n≡n' =
    let [n]  = neu neN  (univ n)
        [n'] = neu neN' (univ n')
    in  Uₜ₌ _ _ (idRedTerm:*: n) (idRedTerm:*: n') (ne neN) (ne neN')
            n≡n' [n] [n'] (neuEq [n] neN neN' (univ n) (univ n') (≅-univ n≡n'))
  neuEqTerm (ℕ [ ⊢A , ⊢B , D ]) neN neN' n n' n≡n' =
    let A≡ℕ = subset* D
    in  ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n' A≡ℕ))
            (≅-conv n≡n' A≡ℕ) (ne (neNfₜ₌ neN neN' (≅-conv n≡n' A≡ℕ)))
  neuEqTerm (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neN neN' n n' n≡n' =
    let A≡K = subset* D
    in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n' A≡K))
             (neNfₜ₌ neN neN' (≅-conv n≡n' A≡K))
  neuEqTerm (Π (Π F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) neN neN' n n' n≡n' =
    let [ΠFG] = Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n' A≡ΠFG))
            (ne neN) (ne neN') (≅-conv n≡n' A≡ΠFG)
            (neuTerm [ΠFG] neN n) (neuTerm [ΠFG] neN' n')
            (λ {ρ} [ρ] ⊢Δ [a] →
               let ρA≡ρΠFG = wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = wkTerm [ρ] ⊢Δ n
                   ρn' = wkTerm [ρ] ⊢Δ n'
                   a = wellformedTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = wellformedTermEq ([F] [ρ] ⊢Δ)
                                          (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = _∘_ (wkNeutral ρ neN)
                   neN'∙a' = _∘_ (wkNeutral ρ neN')
               in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN'∙a'
                             (conv ρn  ρA≡ρΠFG ∘ a)
                             (conv ρn' ρA≡ρΠFG ∘ a)
                             (≅-app-cong (≅ₜ-wk [ρ] ⊢Δ (≅-conv n≡n' A≡ΠFG)) a≡a))
  neuEqTerm (emb 0<1 x) neN neN' n:≡:n' = neuEqTerm x neN neN' n:≡:n'
