{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- Helper function for symmetry of type equality using shape views.
  symEqT : ∀ {A B l l′} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
         → ShapeView Γ l l′ A B [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B / [A]
         → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEqT (ℕᵥ D D′) A≡B = red D
  symEqT (Emptyᵥ D D′) A≡B = red D
  symEqT (Unitᵥ D D′) A≡B = red D
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
         rewrite whrDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK
        (~-sym K≡M)
  symEqT {Γ = Γ} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , ⟦ W ⟧ₙ) (D′ , ⟦ W ⟧ₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity W ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {ℓ} {Δ : Con Term ℓ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {_} {Δ} {ρ} [ρ] ⊢Δ =
          let [ρF′] = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Γ = Δ} (PE.cong (wk ρ) (PE.sym F₁≡F′))
                             [ρF′] ([F]₁ [ρ] ⊢Δ)
                             (symEq ([F] [ρ] ⊢Δ) [ρF′]
                                    ([F≡F′] [ρ] ⊢Δ))
    in  B₌ _ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ x) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B))
          [F₁≡F]
          (λ {_} {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ]) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT {Γ = Γ} (∪ᵥ (∪ᵣ F G D ⊢F ⊢G A≡A [F] [G]) (∪ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁))
                 (∪₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , ∪ₙ) (D′ , ∪ₙ)
        F₁≡F′ , G₁≡G′ = ∪-PE-injectivity ΠF₁G₁≡ΠF′G′
    in ∪₌ _ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ F ∪ G ≅ x) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B))
          (λ {m} {ρ} {Δ} [ρ] ⊢Δ →
            irrelevanceEq′ {Γ = Δ} (PE.cong (wk ρ) (PE.sym F₁≡F′))
                           (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)) ([F]₁ [ρ] ⊢Δ)
                           (symEq ([F] [ρ] ⊢Δ) (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)) ([F≡F′] [ρ] ⊢Δ)))
          (λ {m} {ρ} {Δ} [ρ] ⊢Δ →
            irrelevanceEq′ {Γ = Δ} (PE.cong (wk ρ) (PE.sym G₁≡G′))
                           (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) G₁≡G′ ([G]₁ [ρ] ⊢Δ)) ([G]₁ [ρ] ⊢Δ)
                           (symEq ([G] [ρ] ⊢Δ) (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) G₁≡G′ ([G]₁ [ρ] ⊢Δ)) ([G≡G′] [ρ] ⊢Δ)))
  symEqT {Γ = Γ} (∥ᵥ (∥ᵣ F D ⊢F A≡A [F]) (∥ᵣ F₁ D₁ ⊢F₁ A≡A₁ [F]₁))
                 (∥₌ F′ D′ A≡B [F≡F′]) =
    let ∥F₁≡∥F′ = whrDet* (red D₁ , ∥ₙ) (D′ , ∥ₙ)
        F₁≡F′   = ∥-PE-injectivity ∥F₁≡∥F′
    in ∥₌ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ ∥ F ∥ ≅ x) (PE.sym ∥F₁≡∥F′) A≡B))
          (λ {m} {ρ} {Δ} [ρ] ⊢Δ →
            irrelevanceEq′ {Γ = Δ} (PE.cong (wk ρ) (PE.sym F₁≡F′))
                           (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)) ([F]₁ [ρ] ⊢Δ)
                           (symEq ([F] [ρ] ⊢Δ) (PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)) ([F≡F′] [ρ] ⊢Δ)))
  symEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  -- Symmetry of type equality.
  symEq : ∀ {A B l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
        → Γ ⊩⟨ l ⟩ A ≡ B / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symNatural-prop : ∀ {k k′}
                → [Natural]-prop Γ k k′
                → [Natural]-prop Γ k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symEmpty-prop : ∀ {k k′}
              → [Empty]-prop Γ k k′
              → [Empty]-prop Γ k′ k
symEmpty-prop (ne prop) = ne (symNeutralTerm prop)

sym[Unit]-prop : ∀ {k k′}
               → [Unit]-prop Γ k k′
               → [Unit]-prop Γ k′ k
sym[Unit]-prop (u , v) = v , u
{--
sym[Unit]-prop starᵣ = starᵣ
sym[Unit]-prop (ne prop) = ne (symNeutralTerm prop)
--}

-- Symmetry of term equality.
symEqTerm : ∀ {l A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A d′ d typeB typeA (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symEmpty-prop prop)
symEqTerm (Unitᵣ D) (Unitₜ₌ k k′ d d′ k≡k′ prop) =
  Unitₜ₌ k′ k d′ d (≅ₜ-sym k≡k′) (sym[Unit]-prop prop)
symEqTerm (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
  let ⊢Γ = wf ⊢F
      [Gfstp≡Gfstr] = G-ext Wk.id ⊢Γ [fstp] [fstr] [fst≡]
  in  Σₜ₌ r p d′ d rProd pProd (≅ₜ-sym p≅r) [u] [t] [fstr] [fstp]
          (symEqTerm ([F] Wk.id ⊢Γ) [fst≡])
          (convEqTerm₁
            ([G] Wk.id ⊢Γ [fstp]) ([G] Wk.id ⊢Γ [fstr])
            [Gfstp≡Gfstr]
            (symEqTerm ([G] Wk.id ⊢Γ [fstp]) [snd≡]))
symEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
          (∪₁ₜ₌ p r c d p≅r e f pa ra i j x) =
  ∪₁ₜ₌ r p d c (≅ₜ-sym p≅r) f e ra pa j i (symEqTerm ([F] Wk.id (wf ⊢F)) x)
symEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
          (∪₂ₜ₌ p r c d p≅r e f pa ra i j x) =
  ∪₂ₜ₌ r p d c (≅ₜ-sym p≅r) f e ra pa j i (symEqTerm ([G] Wk.id (wf ⊢G)) x)
symEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
          (∪₃ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k)) =
  ∪₃ₜ₌ r p d c (≅ₜ-sym p≅r) f e (neNfₜ₌ neL neK (~-sym k≡k))
symEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
          (∥₁ₜ₌ p r c d p≅r e f pa ra i j x) =
  ∥₁ₜ₌ r p d c (≅ₜ-sym p≅r) f e ra pa j i (symEqTerm ([F] Wk.id (wf ⊢F)) x)
symEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
          (∥₂ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k)) =
  ∥₂ₜ₌ r p d c (≅ₜ-sym p≅r) f e (neNfₜ₌ neL neK (~-sym k≡k))
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
