{-# OPTIONS --without-K #-}

open import Definition.EqualityRelation

module Definition.LogicalRelation.Properties.Transitivity {{eqrel : EqRelSet}} where
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
  transEqT : ∀ {Γ A B C l l' l''}
             {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l' ⟩ B} {[C] : Γ ⊩⟨ l'' ⟩ C}
           → Tactic Γ l  l'  A B [A] [B]
           → Tactic Γ l' l'' B C [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l' ⟩ B ≡ C / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEqT (ℕ D D') (ℕ _ D'') A≡B B≡C = B≡C
  transEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne ._ (ne K₂ D₂ neK₂ K≡K₂))
           (ne₌ M D' neM K≡M) (ne₌ M₁ D'' neM₁ K≡M₁)
           rewrite whrDet*' (red D₁ , ne neK₁) (red D' , ne neM)
                 | whrDet*' (red D₂ , ne neK₂) (red D'' , ne neM₁) =
    ne₌ M₁  D''  neM₁
        (≅-trans K≡M K≡M₁)
  transEqT {Γ} {l = l} {l' = l′} {l'' = l″}
           (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)
              (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
           (Π ._ (Π F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
           (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (Π₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let F₁≡F′  , G₁≡G′  = Π-PE-injectivity (whrDet*' (red D₁ , Π) (D′  , Π))
        F₂≡F″ , G₂≡G″ = Π-PE-injectivity (whrDet*' (red D₂ , Π) (D″ , Π))
        substLift {Δ} {l} {a} ρ x = Δ ⊩⟨ l ⟩ U.wk (lift ρ) x [ a ]
        [F′] : ∀ {ρ Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ U.wk ρ F′
        [F′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ U.wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ U.wk ρ F″
        [F″] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ U.wk ρ x) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ U.wk ρ F′ ≡ U.wk ρ F″ / [F′] [ρ] ⊢Δ
        [F′≡F″] {ρ} [ρ] ⊢Δ = irrelevanceEq' (PE.cong (U.wk ρ) F₁≡F′)
                                      ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ U.wk ρ F′ / [F′] [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ U.wk (lift ρ) G′ [ a ]
        [G′] {ρ} [ρ] ⊢Δ [a] =
          let [a′] = irrelevanceTerm' (PE.cong (U.wk ρ) (PE.sym F₁≡F′))
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₁≡G′ ([G]₁ [ρ] ⊢Δ [a′])
        [G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ U.wk ρ F″ / [F″] [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ U.wk (lift ρ) G″ [ a ]
        [G″] {ρ} [ρ] ⊢Δ [a] =
          let [a″] = irrelevanceTerm' (PE.cong (U.wk ρ) (PE.sym F₂≡F″))
                                      ([F″] [ρ] ⊢Δ) ([F]₂ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₂≡G″ ([G]₂ [ρ] ⊢Δ [a″])
        [G′≡G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ U.wk ρ F′ / [F′] [ρ] ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ U.wk (lift ρ) G′  [ a ]
                          ≡ U.wk (lift ρ) G″ [ a ] / [G′] [ρ] ⊢Δ [a]
        [G′≡G″] {ρ} [ρ] ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm' (PE.cong (U.wk ρ) (PE.sym F₁≡F′))
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a′]
          in  irrelevanceEq' (PE.cong (λ x → U.wk (lift ρ) x [ _ ]) G₁≡G′)
                             ([G]₁ [ρ] ⊢Δ [a]₁) ([G′] [ρ] ⊢Δ [a′])
                             ([G≡G′]₁ [ρ] ⊢Δ [a]₁)
    in  Π₌ F″ G″ D″ (≅-trans A≡B A≡B₁)
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


transEqTermNe : ∀ {Γ n n' n'' A}
              → Γ ⊩neNf n  ≡ n'  ∷ A
              → Γ ⊩neNf n' ≡ n'' ∷ A
              → Γ ⊩neNf n  ≡ n'' ∷ A
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (≅ₜ-trans k≡m k≡m₁)

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
    in  ℕₜ₌ k k'' d d'' (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k' t≡u₁))
            (transNatural-prop prop prop')

  transNatural-prop : ∀ {Γ k k' k''}
                    → [Natural]-prop Γ k k'
                    → [Natural]-prop Γ k' k''
                    → [Natural]-prop Γ k k''
  transNatural-prop (suc x) (suc x₁) = suc (transEqTermℕ x x₁)
  transNatural-prop (suc x) (ne (neNfₜ₌ () neM k≡m))
  transNatural-prop zero prop₁ = prop₁
  transNatural-prop prop zero = prop
  transNatural-prop (ne (neNfₜ₌ neK () k≡m)) (suc x₃)
  transNatural-prop (ne [k≡k']) (ne [k'≡k'']) = ne (transEqTermNe [k≡k'] [k'≡k''])

transEqTerm : ∀ {l Γ A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]
transEqTerm (U' .⁰ 0<1 ⊢Γ)
            (Uₜ₌ A B d d' typeA typeB t≡u [t] [u] [t≡u])
            (Uₜ₌ A₁ B₁ d₁ d₁' typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁)
            rewrite whrDet* (redₜ d' , typeWhnf typeB) (redₜ d₁ , typeWhnf typeA₁) =
  Uₜ₌ A B₁ d d₁' typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁
      (transEq [t] [u] [u]₁ [t≡u] (irrelevanceEq [t]₁ [u] [t≡u]₁))
transEqTerm (ℕ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
transEqTerm (ne' K D neK K≡K) (neₜ₌ k m d d' (neNfₜ₌ neK₁ neM k≡m))
                              (neₜ₌ k₁ m₁ d₁ d'' (neNfₜ₌ neK₂ neM₁ k≡m₁)) =
  let k₁≡m = whrDet* (redₜ d₁ , ne neK₂) (redₜ d' , ne neM)
  in  neₜ₌ k m₁ d d''
           (neNfₜ₌ neK₁ neM₁
                   (≅ₜ-trans k≡m (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡m k≡m₁)))
transEqTerm (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Πₜ₌ f g d d' funcF funcG f≡g [f] [g] [f≡g])
            (Πₜ₌ f₁ g₁ d₁ d₁' funcF₁ funcG₁ f≡g₁ [f]₁ [g]₁ [f≡g]₁)
            rewrite whrDet* (redₜ d' , functionWhnf funcG)
                            (redₜ d₁ , functionWhnf funcF₁) =
  Πₜ₌ f g₁ d d₁' funcF funcG₁ (≅ₜ-trans f≡g f≡g₁) [f] [g]₁
      (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
                                ([f≡g] ρ ⊢Δ [a])
                                ([f≡g]₁ ρ ⊢Δ [a]))
transEqTerm (emb 0<1 x) t≡u u≡v = transEqTerm x t≡u u≡v
