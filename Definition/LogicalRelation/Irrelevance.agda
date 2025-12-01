{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
import Definition.Typed.Weakening as Wk
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView

open import Tools.Nat
open import Tools.Product
open import Tools.Sum
  using (_⊎_ ; inj₁ ; inj₂)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Γ′ : Con Term n

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A
              → Γ′ ⊩⟨ l ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B l l′} (eq : A PE.≡ A′)
                   (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                 → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types and
  -- a lifting of propositionally equal types
  irrelevanceEqLift″ : ∀ {A A′ B B′ C C′ l l′}
                        (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
                        (p : Γ ∙ C ⊩⟨ l ⟩ A) (q : Γ ∙ C′ ⊩⟨ l′ ⟩ A′)
                      → Γ ∙ C ⊩⟨ l ⟩ A ≡ B / p → Γ ∙ C′ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView Γ l l′ A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
    ne₌ M D′ neM K≡M
  irrelevanceEqT {Γ = Γ} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity W ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ D′ (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {_} {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) ([F] [ρ] ⊢Δ)
                                    ([F]₁ [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
           (λ {_} {ρ} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
  irrelevanceEqT {Γ = Γ} (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁)) (∪₌ S′ T′ D′ A≡B [S≡S′] [T≡T′]) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in  ∪₌ S′ T′ D′
           (PE.subst (λ x → Γ ⊢ x ≅ (S′ ∪ T′)) ∪ST≡∪S₁T₁ A≡B)
           (λ {_} {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) S≡S₁) ([S] [ρ] ⊢Δ)
                                              ([S]₁ [ρ] ⊢Δ) ([S≡S′] [ρ] ⊢Δ))
           (λ {_} {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) T≡T₁) ([T] [ρ] ⊢Δ)
                                              ([T]₁ [ρ] ⊢Δ) ([T≡T′] [ρ] ⊢Δ))
  irrelevanceEqT {Γ = Γ} (∥ᵥ (∥ᵣ S D ⊢S A≡A [S]) (∥ᵣ S₁ D₁ ⊢S₁ A≡A₁ [S]₁)) (∥₌ S′ D′ A≡B [S≡S′]) =
    let ∥S≡∥S₁ = whrDet* (red D , ∥ₙ) (red D₁ , ∥ₙ)
        S≡S₁   = ∥-PE-injectivity ∥S≡∥S₁
    in  ∥₌ S′ D′
           (PE.subst (λ x → Γ ⊢ x ≅ ∥ S′ ∥) ∥S≡∥S₁ A≡B)
           (λ {_} {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) S≡S₁) ([S] [ρ] ⊢Δ)
                                              ([S]₁ [ρ] ⊢Δ) ([S≡S′] [ρ] ⊢Δ))
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                  → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t l l′} (eq : A PE.≡ A′)
                     (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                   → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                    → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {A t l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                         → ShapeView Γ l l′ A A p q
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (Emptyᵥ D D′) t = t
  irrelevanceTermT (Unitᵥ D D′) t = t
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
    in  Πₜ f (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → Γ ⊢ f ≅ f ∷ x) ΠFG≡ΠF₁G₁ f≡f)
           (λ {_} {ρ} [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁ →
              let [a]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                           ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
                  [b]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                           ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [b]₁
                  [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                             ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a≡b]₁
              in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                     ([f] [ρ] ⊢Δ [a] [b] [a≡b]))
          (λ {_} {ρ} [ρ] ⊢Δ [a]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                  ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f]₁ [ρ] ⊢Δ [a]))
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Σₜ p d pProd p≅p [fst] [snd]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        [fst]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                  ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
                                  [fst]
        [snd]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
                                  ([G] Wk.id (wf ⊢F) [fst]) ([G]₁ Wk.id (wf ⊢F₁) [fst]′)
                                  [snd]
    in  Σₜ p (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d) pProd
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p)
           [fst]′ [snd]′
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT {Γ = Γ} {t = t} (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                   (∪₁ₜ p c d pa i e) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₁ₜ p
           (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ∪ST≡∪S₁T₁ d)
           pa i
           (irrelevanceTerm′ (PE.cong (wk id) S≡S₁) ([S] Wk.id (wf ⊢S))
                                  ([S]₁ Wk.id (wf ⊢S₁)) e)
  irrelevanceTermT {Γ = Γ} {t = t} (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                   (∪₂ₜ p c d pa i e) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₂ₜ p
           (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ∪ST≡∪S₁T₁ d)
           pa i
           (irrelevanceTerm′ (PE.cong (wk id) T≡T₁) ([T] Wk.id (wf ⊢T))
                                  ([T]₁ Wk.id (wf ⊢T₁)) e)
  irrelevanceTermT {Γ = Γ} {t = t} (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                   (∪₃ₜ p c d (neNfₜ neK ⊢k k≡k)) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₃ₜ p
           (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ∪ST≡∪S₁T₁ d)
           (neNfₜ neK
                  (PE.subst (λ x → Γ ⊢ p ∷ x) ∪ST≡∪S₁T₁ ⊢k)
                  (PE.subst (λ x → Γ ⊢ p ~ p ∷ x) ∪ST≡∪S₁T₁ k≡k))
  irrelevanceTermT {Γ = Γ} {t = t} (∥ᵥ (∥ᵣ S D ⊢S A≡A [S]) (∥ᵣ S₁ D₁ ⊢S₁ A≡A₁ [S]₁))
                   (∥₁ₜ p c d pa i e) =
    let ∥S≡∥S₁ = whrDet* (red D , ∥ₙ) (red D₁ , ∥ₙ)
        S≡S₁   = ∥-PE-injectivity ∥S≡∥S₁
    in ∥₁ₜ p
           (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∥S≡∥S₁ c)
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ∥S≡∥S₁ d)
           pa i
           (irrelevanceTerm′ (PE.cong (wk id) S≡S₁) ([S] Wk.id (wf ⊢S))
                             ([S]₁ Wk.id (wf ⊢S₁)) e)
  irrelevanceTermT {Γ = Γ} {t = t} (∥ᵥ (∥ᵣ S D ⊢S A≡A [S]) (∥ᵣ S₁ D₁ ⊢S₁ A≡A₁ [S]₁))
                   (∥₂ₜ p c d (neNfₜ neK ⊢k k≡k)) =
    let ∥S≡∥S₁ = whrDet* (red D , ∥ₙ) (red D₁ , ∥ₙ)
        S≡S₁   = ∥-PE-injectivity ∥S≡∥S₁
    in ∥₂ₜ p
           (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∥S≡∥S₁ c)
           (PE.subst (λ x → Γ ⊢ p ≅ p ∷ x) ∥S≡∥S₁ d)
           (neNfₜ neK
                  (PE.subst (λ x → Γ ⊢ p ∷ x) ∥S≡∥S₁ ⊢k)
                  (PE.subst (λ x → Γ ⊢ p ~ p ∷ x) ∥S≡∥S₁ k≡k))
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u l l′} (eq : A PE.≡ A′)
                       (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                           → ShapeView Γ l l′ A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
        [A]         = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ f g (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: g ∷ x) ΠFG≡ΠF₁G₁ d′) funcF funcG
            (PE.subst (λ x → Γ ⊢ f ≅ g ∷ x) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            (λ {_} {ρ} [ρ] ⊢Δ [a]₁ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                          ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a]))
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        [A]         = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                   ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
                                   [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                   ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
                                   [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                     ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
                                     [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
                                     ([G] Wk.id (wf ⊢F) [fstp]) ([G]₁ Wk.id (wf ⊢F₁) [fstp]′)
                                     [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            [fstp]′
            [fstr]′
            [fst≡]′
            [snd≡]′
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                     (∪₁ₜ₌ p r c d e f g pa ra i j z) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₁ₜ₌ p r
            (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ∪ST≡∪S₁T₁ d)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ∪ST≡∪S₁T₁ e)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) f)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) g)
            pa ra i j
            (irrelevanceEqTerm′ (PE.cong (wk id) S≡S₁) ([S] Wk.id (wf ⊢S))
                                ([S]₁ Wk.id (wf ⊢S₁)) z)
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                     (∪₂ₜ₌ p r c d e f g pa ra i j z) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₂ₜ₌ p r
            (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ∪ST≡∪S₁T₁ d)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ∪ST≡∪S₁T₁ e)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) f)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) g)
            pa ra i j
            (irrelevanceEqTerm′ (PE.cong (wk id) T≡T₁) ([T] Wk.id (wf ⊢T))
                                ([T]₁ Wk.id (wf ⊢T₁)) z)
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (∪ᵥ (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁))
                     (∪₃ₜ₌ p r c d e f g (neNfₜ₌ neK neL k≡k)) =
    let ∪ST≡∪S₁T₁   = whrDet* (red D , ∪ₙ) (red D₁ , ∪ₙ)
        S≡S₁ , T≡T₁ = ∪-PE-injectivity ∪ST≡∪S₁T₁
    in ∪₃ₜ₌ p r
            (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∪ST≡∪S₁T₁ c)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ∪ST≡∪S₁T₁ d)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ∪ST≡∪S₁T₁ e)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) f)
            (irrelevanceTerm (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (∪ᵣ′ S₁ T₁ D₁ ⊢S₁ ⊢T₁ A≡A₁ [S]₁ [T]₁) g)
            (neNfₜ₌ neK neL (PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ∪ST≡∪S₁T₁ k≡k))
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (∥ᵥ (∥ᵣ S D ⊢S A≡A [S]) (∥ᵣ S₁ D₁ ⊢S₁ A≡A₁ [S]₁))
                     (∥₁ₜ₌ p r c d e f g pa ra i j z) =
    let ∥S≡∥S₁ = whrDet* (red D , ∥ₙ) (red D₁ , ∥ₙ)
        S≡S₁   = ∥-PE-injectivity ∥S≡∥S₁
    in ∥₁ₜ₌ p r
            (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∥S≡∥S₁ c)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ∥S≡∥S₁ d)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ∥S≡∥S₁ e)
            (irrelevanceTerm (∥ᵣ′ S D ⊢S A≡A [S]) (∥ᵣ′ S₁ D₁ ⊢S₁ A≡A₁ [S]₁) f)
            (irrelevanceTerm (∥ᵣ′ S D ⊢S A≡A [S]) (∥ᵣ′ S₁ D₁ ⊢S₁ A≡A₁ [S]₁) g)
            pa ra i j
            (irrelevanceEqTerm′ (PE.cong (wk id) S≡S₁) ([S] Wk.id (wf ⊢S))
                                ([S]₁ Wk.id (wf ⊢S₁)) z)
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (∥ᵥ (∥ᵣ S D ⊢S A≡A [S]) (∥ᵣ S₁ D₁ ⊢S₁ A≡A₁ [S]₁))
                     (∥₂ₜ₌ p r c d e f g (neNfₜ₌ neK neL k≡k)) =
    let ∥S≡∥S₁ = whrDet* (red D , ∥ₙ) (red D₁ , ∥ₙ)
        S≡S₁   = ∥-PE-injectivity ∥S≡∥S₁
    in ∥₂ₜ₌ p r
            (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ∥S≡∥S₁ c)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ∥S≡∥S₁ d)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ∥S≡∥S₁ e)
            (irrelevanceTerm (∥ᵣ′ S D ⊢S A≡A [S]) (∥ᵣ′ S₁ D₁ ⊢S₁ A≡A₁ [S]₁) f)
            (irrelevanceTerm (∥ᵣ′ S D ⊢S A≡A [S]) (∥ᵣ′ S₁ D₁ ⊢S₁ A≡A₁ [S]₁) g)
            (neNfₜ₌ neK neL (PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ∥S≡∥S₁ k≡k))
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
