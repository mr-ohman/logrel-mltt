{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Transitivity {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion
open import Definition.LogicalRelation.Properties.Symmetry

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- Helper function for transitivity of type equality using shape views.
  transEqT : ∀ {n} {Γ : Con Term n} {A B C l l′ l″}
             {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B} {[C] : Γ ⊩⟨ l″ ⟩ C}
           → ShapeView₃ Γ l l′ l″ A B C [A] [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEqT (ℕᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Emptyᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Unitᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K) (ne K₁ D₁ neK₁ _)
               (ne K₂ D₂ neK₂ _))
           (ne₌ M D′ neM K≡M) (ne₌ M₁ D″ neM₁ K≡M₁)
           rewrite whrDet* (red D₁ , ne neK₁) (red D′ , ne neM)
                 | whrDet* (red D₂ , ne neK₂) (red D″ , ne neM₁) =
    ne₌ M₁ D″ neM₁
        (~-trans K≡M K≡M₁)
  transEqT {n} {Γ} {l = l} {l′ = l′} {l″ = l″}
           (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
                 (Bᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
           (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (B₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let ΠF₁G₁≡ΠF′G′    = whrDet* (red D₁ , ⟦ W ⟧ₙ) (D′  , ⟦ W ⟧ₙ)
        F₁≡F′  , G₁≡G′ = B-PE-injectivity W ΠF₁G₁≡ΠF′G′
        F₂≡F″ , G₂≡G″  = B-PE-injectivity W (whrDet* (red D₂ , ⟦ W ⟧ₙ) (D″ , ⟦ W ⟧ₙ))
        substLift : ∀ {m n Δ l a} (ρ : Wk m n) x → Set
        substLift {_} {_} {Δ} {l} {a} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ]
        [F′] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′
        [F′] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″
        [F″] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ / [F′] [ρ] ⊢Δ
        [F′≡F″] {_} {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′)
                                      ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {m} {ρ : Wk m n} {Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ / [F′] [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′ [ a ]
        [G′] {m} {ρ} [ρ] ⊢Δ [a] =
          let [a′] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₁≡G′ ([G]₁ [ρ] ⊢Δ [a′])
        [G″] : ∀ {m} {ρ : Wk m n} {Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ wk ρ F″ / [F″] [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ wk (lift ρ) G″ [ a ]
        [G″] {_} {ρ} [ρ] ⊢Δ [a] =
          let [a″] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₂≡F″))
                                      ([F″] [ρ] ⊢Δ) ([F]₂ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₂≡G″ ([G]₂ [ρ] ⊢Δ [a″])
        [G′≡G″] : ∀ {m} {ρ : Wk m n} {Δ a} [ρ] ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ / [F′] [ρ] ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′  [ a ]
                          ≡ wk (lift ρ) G″ [ a ] / [G′] [ρ] ⊢Δ [a]
        [G′≡G″] {_} {ρ} [ρ] ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a′]
          in  irrelevanceEq′ (PE.cong (λ x → wk (lift ρ) x [ _ ]) G₁≡G′)
                             ([G]₁ [ρ] ⊢Δ [a]₁) ([G′] [ρ] ⊢Δ [a′])
                             ([G≡G′]₁ [ρ] ⊢Δ [a]₁)
    in  B₌ F″ G″ D″ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W ⟧ F″ ▹ G″) ΠF₁G₁≡ΠF′G′ A≡B₁))
           (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
                             ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
           (λ ρ ⊢Δ [a] →
              let [a′] = convTerm₁ ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                  [a″] = convTerm₁ ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
              in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                          ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′]))
  transEqT {n} {Γ} {l = l} {l′ = l′} {l″ = l″}
           (∪ᵥ (∪ᵣ F G D ⊢F ⊢G A≡A [F] [G])
               (∪ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁)
               (∪ᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂))
           (∪₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (∪₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let ΠF₁G₁≡ΠF′G′    = whrDet* (red D₁ , ∪ₙ) (D′  , ∪ₙ)
        F₁≡F′  , G₁≡G′ = ∪-PE-injectivity ΠF₁G₁≡ΠF′G′
        F₂≡F″ , G₂≡G″  = ∪-PE-injectivity (whrDet* (red D₂ , ∪ₙ) (D″ , ∪ₙ))
        substLift : ∀ {m n Δ l a} (ρ : Wk m n) x → Set
        substLift {_} {_} {Δ} {l} {a} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ]
        [F′] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′
        [F′] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″
        [F″] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ / [F′] [ρ] ⊢Δ
        [F′≡F″] {_} {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′) ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ G′
        [G′] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) G₁≡G′ ([G]₁ [ρ] ⊢Δ)
        [G″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ G″
        [G″] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) G₂≡G″ ([G]₂ [ρ] ⊢Δ)
        [G′≡G″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ G′ ≡ wk ρ G″ / [G′] [ρ] ⊢Δ
        [G′≡G″] {_} {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) G₁≡G′) ([G]₁ [ρ] ⊢Δ) ([G′] [ρ] ⊢Δ) ([G≡G′]₁ [ρ] ⊢Δ)
    in ∪₌ F″ G″ D″ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ F″ ∪ G″) ΠF₁G₁≡ΠF′G′ A≡B₁))
          (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
                             ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
          (λ ρ ⊢Δ → transEq ([G] ρ ⊢Δ) ([G′] ρ ⊢Δ) ([G″] ρ ⊢Δ)
                             ([G≡G′] ρ ⊢Δ) ([G′≡G″] ρ ⊢Δ))
  transEqT {n} {Γ} {l = l} {l′ = l′} {l″ = l″}
           (∥ᵥ (∥ᵣ F D ⊢F A≡A [F])
               (∥ᵣ F₁ D₁ ⊢F₁ A≡A₁ [F]₁)
               (∥ᵣ F₂ D₂ ⊢F₂ A≡A₂ [F]₂))
           (∥₌ F′ D′ A≡B [F≡F′])
           (∥₌ F″ D″ A≡B₁ [F≡F′]₁) =
    let ∥F₁≡∥F′ = whrDet* (red D₁ , ∥ₙ) (D′  , ∥ₙ)
        F₁≡F′   = ∥-PE-injectivity ∥F₁≡∥F′
        F₂≡F″   = ∥-PE-injectivity (whrDet* (red D₂ , ∥ₙ) (D″ , ∥ₙ))
        substLift : ∀ {m n Δ l a} (ρ : Wk m n) x → Set
        substLift {_} {_} {Δ} {l} {a} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ]
        [F′] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′
        [F′] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″
        [F″] {_} {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {m} {ρ : Wk m n} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ / [F′] [ρ] ⊢Δ
        [F′≡F″] {_} {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′) ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
    in ∥₌ F″ D″ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ ∥ F″ ∥) ∥F₁≡∥F′ A≡B₁))
          (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
                             ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
  transEqT (Uᵥ ⊢Γ ⊢Γ₁ ⊢Γ₂) A≡B B≡C = A≡B
  transEqT (emb⁰¹¹ AB) A≡B B≡C = transEqT AB A≡B B≡C
  transEqT (emb¹⁰¹ AB) A≡B B≡C = transEqT AB A≡B B≡C
  transEqT (emb¹¹⁰ AB) A≡B B≡C = transEqT AB A≡B B≡C

  -- Transitivty of type equality.
  transEq : ∀ {A B C l l′ l″}
            ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B) ([C] : Γ ⊩⟨ l″ ⟩ C)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
          → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEq [A] [B] [C] A≡B B≡C =
    transEqT (combine (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C)) A≡B B≡C

  -- Transitivty of type equality with some propositonally equal types.
  transEq′ : ∀ {A B B′ C C′ l l′ l″} → B PE.≡ B′ → C PE.≡ C′
           → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B) ([C] : Γ ⊩⟨ l″ ⟩ C)
           → Γ ⊩⟨ l ⟩  A ≡ B′ / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C′ / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C  / [A]
  transEq′ PE.refl PE.refl [A] [B] [C] A≡B B≡C = transEq [A] [B] [C] A≡B B≡C


transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′  ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermℕ : ∀ {n n′ n″}
               → Γ ⊩ℕ n  ≡ n′  ∷ℕ
               → Γ ⊩ℕ n′ ≡ n″ ∷ℕ
               → Γ ⊩ℕ n  ≡ n″ ∷ℕ
  transEqTermℕ (ℕₜ₌ k k′ d d′ t≡u prop)
               (ℕₜ₌ k₁ k″ d₁ d″ t≡u₁ prop₁) =
    let k₁Whnf = naturalWhnf (proj₁ (split prop₁))
        k′Whnf = naturalWhnf (proj₂ (split prop))
        k₁≡k′ = whrDet*Term (redₜ d₁ , k₁Whnf) (redₜ d′ , k′Whnf)
        prop′ = PE.subst (λ x → [Natural]-prop _ x _) k₁≡k′ prop₁
    in  ℕₜ₌ k k″ d d″ (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
            (transNatural-prop prop prop′)

  transNatural-prop : ∀ {k k′ k″}
                    → [Natural]-prop Γ k k′
                    → [Natural]-prop Γ k′ k″
                    → [Natural]-prop Γ k k″
  transNatural-prop (sucᵣ x) (sucᵣ x₁) = sucᵣ (transEqTermℕ x x₁)
  transNatural-prop (sucᵣ x) (ne (neNfₜ₌ () neM k≡m))
  transNatural-prop zeroᵣ prop₁ = prop₁
  transNatural-prop prop zeroᵣ = prop
  transNatural-prop (ne (neNfₜ₌ neK () k≡m)) (sucᵣ x₃)
  transNatural-prop (ne [k≡k′]) (ne [k′≡k″]) =
    ne (transEqTermNe [k≡k′] [k′≡k″])

-- Empty
transEmpty-prop : ∀ {k k′ k″}
  → [Empty]-prop Γ k k′
  → [Empty]-prop Γ k′ k″
  → [Empty]-prop Γ k k″
transEmpty-prop (ne [k≡k′]) (ne [k′≡k″]) =
  ne (transEqTermNe [k≡k′] [k′≡k″])

transEqTermEmpty : ∀ {n n′ n″}
  → Γ ⊩Empty n  ≡ n′ ∷Empty
  → Γ ⊩Empty n′ ≡ n″ ∷Empty
  → Γ ⊩Empty n  ≡ n″ ∷Empty
transEqTermEmpty (Emptyₜ₌ k k′ d d′ t≡u prop)
                 (Emptyₜ₌ k₁ k″ d₁ d″ t≡u₁ prop₁) =
  let k₁Whnf = ne (proj₁ (esplit prop₁))
      k′Whnf = ne (proj₂ (esplit prop))
      k₁≡k′ = whrDet*Term (redₜ d₁ , k₁Whnf) (redₜ d′ , k′Whnf)
      prop′ = PE.subst (λ x → [Empty]-prop _ x _) k₁≡k′ prop₁
  in Emptyₜ₌ k k″ d d″ (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
     (transEmpty-prop prop prop′)

trans[Unit]-prop : ∀ {k k′ k″}
                 → [Unit]-prop Γ k k′
                 → [Unit]-prop Γ k′ k″
                 → [Unit]-prop Γ k k″
trans[Unit]-prop {k} {k′} {k″} (u , v) (w , x) = u , x
{--
trans[Unit]-prop {k} {k′} {.star} starᵣ starᵣ = starᵣ
trans[Unit]-prop {k} {k′} {k″} (ne x) (ne x₁) = ne (transEqTermNe x x₁)
--}

transEqTermUnit : ∀ {t u v}
                → Γ ⊩Unit t ≡ u ∷Unit
                → Γ ⊩Unit u ≡ v ∷Unit
                → Γ ⊩Unit t ≡ v ∷Unit
transEqTermUnit {t} {u} {v} (Unitₜ₌ k k′ d d′ k≡k′ prop)
                            (Unitₜ₌ l l′ e e′ l≡l′ prop₁) =
  let k₁Whnf = nunitWhnf (proj₁ (usplit prop₁))
      k′Whnf = nunitWhnf (proj₂ (usplit prop))
      k₁≡k′  = whrDet*Term (redₜ e , k₁Whnf) (redₜ d′ , k′Whnf)
      prop′  = PE.subst (λ x → [Unit]-prop _ x _) k₁≡k′ prop₁
  in Unitₜ₌ k l′ d e′ (≅ₜ-trans k≡k′ (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k′ l≡l′))
            (trans[Unit]-prop prop prop′)

-- Transitivty of term equality.
transEqTerm : ∀ {l A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]
transEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ)
            (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
            (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁)
            rewrite whrDet*Term (redₜ d′ , typeWhnf typeB) (redₜ d₁ , typeWhnf typeA₁) =
  Uₜ₌ A B₁ d d₁′ typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁
      (transEq [t] [u] [u]₁ [t≡u] (irrelevanceEq [t]₁ [u] [t≡u]₁))
transEqTerm (ℕᵣ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
transEqTerm (Emptyᵣ D) [t≡u] [u≡v] = transEqTermEmpty [t≡u] [u≡v]
transEqTerm (Unitᵣ D) [t≡u] [u≡v] = transEqTermUnit [t≡u] [u≡v]
-- (Unitₜ₌ k k′ d d′ k≡k′ prop) (Unitₜ₌ l l′ e e′ l≡l′ prop₁) =
--  Unitₜ₌ {!!} {!!} {!!} {!!} {!!} {!!}
transEqTerm (ne′ K D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ neK₁ neM k≡m))
                              (neₜ₌ k₁ m₁ d₁ d″ (neNfₜ₌ neK₂ neM₁ k≡m₁)) =
  let k₁≡m = whrDet*Term (redₜ d₁ , ne neK₂) (redₜ d′ , ne neM)
  in  neₜ₌ k m₁ d d″
           (neNfₜ₌ neK₁ neM₁
                   (~-trans k≡m (PE.subst (λ x → _ ⊢ x ~ _ ∷ _) k₁≡m k≡m₁)))
transEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g])
            (Πₜ₌ f₁ g₁ d₁ d₁′ funcF₁ funcG₁ f≡g₁ [f]₁ [g]₁ [f≡g]₁)
            rewrite whrDet*Term (redₜ d′ , functionWhnf funcG)
                                (redₜ d₁ , functionWhnf funcF₁) =
  Πₜ₌ f g₁ d d₁′ funcF funcG₁ (≅ₜ-trans f≡g f≡g₁) [f] [g]₁
      (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
                                ([f≡g] ρ ⊢Δ [a])
                                ([f≡g]₁ ρ ⊢Δ [a]))
transEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡])
            (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ [t]₁ [u]₁ [fstp]₁ [fstr]₁ [fst≡]₁ [snd≡]₁)
            rewrite whrDet*Term (redₜ d′ , productWhnf rProd)
                                (redₜ d₁ , productWhnf pProd₁) =
  let ⊢Γ = wf ⊢F
      [Gfstp≡Gfstp₁] = G-ext Wk.id ⊢Γ [fstp] [fstr] [fst≡]
      [snd≡]′ = transEqTerm ([G] Wk.id ⊢Γ [fstp])
                            [snd≡]
                            (convEqTerm₂ ([G] Wk.id ⊢Γ [fstp])
                                         ([G] Wk.id ⊢Γ [fstp]₁)
                                         [Gfstp≡Gfstp₁]
                                         [snd≡]₁)
  in  Σₜ₌ p r₁ d d₁′ pProd rProd₁ (≅ₜ-trans p≅r p≅r₁) [t] [u]₁ [fstp] [fstr]₁
          (transEqTerm ([F] Wk.id ⊢Γ) [fst≡] [fst≡]₁)
          [snd≡]′
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₁ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₁ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁)
            rewrite whrDet*Term (redₜ d  , injectionLWhnf j)
                                (redₜ c₁ , injectionLWhnf i₁)
                  | InjectionL-PE-injectivity
                      j i₁
                      (whrDet*Term (redₜ d  , injectionLWhnf j)
                                   (redₜ c₁ , injectionLWhnf i₁)) =
  ∪₁ₜ₌ p r₁ c d₁ (≅ₜ-trans p≅r p≅r₁) e f₁ pa ra₁ i j₁
       (transEqTerm ([F] Wk.id (wf ⊢F)) x x₁)
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₂ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₂ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁)
            rewrite whrDet*Term (redₜ d  , injectionRWhnf j)
                                (redₜ c₁ , injectionRWhnf i₁)
                  | InjectionR-PE-injectivity
                      j i₁
                      (whrDet*Term (redₜ d  , injectionRWhnf j)
                                   (redₜ c₁ , injectionRWhnf i₁)) =
  ∪₂ₜ₌ p r₁ c d₁ (≅ₜ-trans p≅r p≅r₁) e f₁ pa ra₁ i j₁
       (transEqTerm ([G] Wk.id (wf ⊢G)) x x₁)
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₁ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₂ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁) =
  ⊥-elim (InjectionL-InjectionR j i₁ (whrDet*Term (redₜ d , injectionLWhnf j) (redₜ c₁ , injectionRWhnf i₁)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₂ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₁ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁) =
  ⊥-elim (InjectionL-InjectionR i₁ j (whrDet*Term (redₜ c₁ , injectionLWhnf i₁) (redₜ d , injectionRWhnf j)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₁ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₃ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ (neNfₜ₌ neK neL k≡k)) =
  ⊥-elim (InjectionL-Neutral j neK (whrDet*Term (redₜ d , injectionLWhnf j) (redₜ c₁ , ne neK)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₂ₜ₌ p r c d p≅r e f pa ra i j x)
            (∪₃ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ (neNfₜ₌ neK neL k≡k)) =
  ⊥-elim (InjectionR-Neutral j neK (whrDet*Term (redₜ d , injectionRWhnf j) (redₜ c₁ , ne neK)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₃ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k))
            (∪₁ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁) =
  ⊥-elim (InjectionL-Neutral i₁ neL (whrDet*Term (redₜ c₁ , injectionLWhnf i₁) (redₜ d , ne neL)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₃ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k))
            (∪₂ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁) =
  ⊥-elim (InjectionR-Neutral i₁ neL (whrDet*Term (redₜ c₁ , injectionRWhnf i₁) (redₜ d , ne neL)))
transEqTerm (∪ᵣ′ F G D ⊢F ⊢G A≡A [F] [G])
            (∪₃ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k))
            (∪₃ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ (neNfₜ₌ neK₁ neL₁ k≡k₁))
            rewrite whrDet*Term (redₜ d  , ne neL)
                                (redₜ c₁ , ne neK₁) =
  ∪₃ₜ₌ p r₁ c d₁ (≅ₜ-trans p≅r p≅r₁) e f₁ (neNfₜ₌ neK neL₁ (~-trans k≡k k≡k₁))
transEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
            (∥₁ₜ₌ p r c d p≅r e f pa ra i j x)
            (∥₁ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁)
            rewrite whrDet*Term (redₜ d  , TruncIWhnf j)
                                (redₜ c₁ , TruncIWhnf i₁)
                  | TruncI-PE-injectivity
                      j i₁
                      (whrDet*Term (redₜ d  , TruncIWhnf j)
                                   (redₜ c₁ , TruncIWhnf i₁)) =
  ∥₁ₜ₌ p r₁ c d₁ (≅ₜ-trans p≅r p≅r₁) e f₁ pa ra₁ i j₁
       (transEqTerm ([F] Wk.id (wf ⊢F)) x x₁)
transEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
            (∥₁ₜ₌ p r c d p≅r e f pa ra i j x)
            (∥₂ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ (neNfₜ₌ neK neL k≡k)) =
  ⊥-elim (TruncI-Neutral j neK (whrDet*Term (redₜ d , TruncIWhnf j) (redₜ c₁ , ne neK)))
transEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
            (∥₂ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k))
            (∥₁ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ pa₁ ra₁ i₁ j₁ x₁) =
  ⊥-elim (TruncI-Neutral i₁ neL (whrDet*Term (redₜ c₁ , TruncIWhnf i₁) (redₜ d , ne neL)))
transEqTerm (∥ᵣ′ F D ⊢F A≡A [F])
            (∥₂ₜ₌ p r c d p≅r e f (neNfₜ₌ neK neL k≡k))
            (∥₂ₜ₌ p₁ r₁ c₁ d₁ p≅r₁ e₁ f₁ (neNfₜ₌ neK₁ neL₁ k≡k₁))
            rewrite whrDet*Term (redₜ d  , ne neL)
                                (redₜ c₁ , ne neK₁) =
  ∥₂ₜ₌ p r₁ c d₁ (≅ₜ-trans p≅r p≅r₁) e f₁ (neNfₜ₌ neK neL₁ (~-trans k≡k k≡k₁))
transEqTerm (emb 0<1 x) t≡u u≡v = transEqTerm x t≡u u≡v
