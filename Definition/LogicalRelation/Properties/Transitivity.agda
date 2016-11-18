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
  transEqT (ℕ (ℕ _) (ℕ _)) (ℕ _ (ℕ _)) A≡B B≡C = B≡C
  transEqT (ne (ne K D neK) (ne K₁ D₁ neK₁)) (ne ._ (ne K₂ D₂ neK₂))
           ne[ M , D' , neM , K≡M ] ne[ M₁ , D'' , neM₁ , K≡M₁ ] =
    ne[ M₁ , D'' , neM₁
      , trans K≡M (trans (trans (sym (subset* (red D')))
                                (subset* (red D₁)))
                         K≡M₁) ]
  transEqT {Γ} {l = l} {l' = l′} {l'' = l″}
           (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)
              (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
           (Π ._ (Π F₂ G₂ D₂ ⊢F₂ ⊢G₂ [F]₂ [G]₂ G-ext₂))
           Π¹[ F′ , G′ , D′ , A≡B , [F≡F′] , [G≡G′] ]
           Π¹[ F″ , G″ , D″ , A≡B₁ , [F≡F′]₁ , [G≡G′]₁ ] =
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
    in  Π¹[ F″ , G″ , D″ , trans A≡B A≡B₁
        , (λ ρ ⊢Δ → transEq ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
                            ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
        , (λ ρ ⊢Δ [a] →
             let [a′] = convTerm₁ ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                 [a″] = convTerm₁ ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
             in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                         ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′])) ]
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
  transEqTermℕ : ∀ {Γ A n n' n''}
               → ℕ[ Γ ] n  ≡ n'  ∷ A
               → ℕ[ Γ ] n' ≡ n'' ∷ A
               → ℕ[ Γ ] n  ≡ n'' ∷ A
  transEqTermℕ ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ]
               ℕ≡[ k₁ , k'' , d₁ , d'' , t≡u₁ , [k≡k']₁ , prop₁ ] =
    let k₁Whnf = naturalWhnf (proj₁ (split [k≡k']₁))
        k'Whnf = naturalWhnf (proj₂ (split [k≡k']))
        k₁≡k' = whrDet* (redₜ d₁ , k₁Whnf) (redₜ d' , k'Whnf)
        [k'≡k''] = PE.subst (λ x → [Natural] x _) k₁≡k' [k≡k']₁
        prop' = irrelevanceNatural-prop k₁≡k' PE.refl [k≡k']₁ [k'≡k''] prop₁
    in  ℕ≡[ k , k'' , d , d'' , trans t≡u t≡u₁ , transNatural [k≡k'] [k'≡k'']
          , transNatural-prop [k≡k'] prop [k'≡k''] prop' ]

  transNatural-prop : ∀ {Γ k k' k''}
                    → ([k≡k'] : [Natural] k k')
                    → [Natural]-prop Γ k k' [k≡k']
                    → ([k'≡k''] : [Natural] k' k'')
                    → [Natural]-prop Γ k' k'' [k'≡k'']
                    → [Natural]-prop Γ k k'' (transNatural [k≡k'] [k'≡k''])
  transNatural-prop suc prop suc prop₁ = transEqTermℕ prop prop₁
  transNatural-prop suc prop (ne () x₁) prop₁
  transNatural-prop zero prop [k'≡k''] prop₁ = prop₁
  transNatural-prop (ne x ()) prop suc prop₁
  transNatural-prop (ne x x₁) prop zero prop₁ = prop
  transNatural-prop (ne x x₁) prop (ne x₂ x₃) prop₁ = trans prop prop₁

transEqTerm : ∀ {l Γ A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]
transEqTerm (U (U .⁰ 0<1 ⊢Γ))
            U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ]
            U[ ⊢t₁ , ⊢u₁ , t≡u₁ , ⊩t₁ , ⊩u₁ , [t≡u]₁ ] =
  U[ ⊢t , ⊢u₁ , trans t≡u t≡u₁ , ⊩t , ⊩u₁
   , transEq ⊩t ⊩u ⊩u₁ [t≡u] (irrelevanceEq ⊩t₁ ⊩u [t≡u]₁) ]
transEqTerm (ℕ (ℕ _)) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
transEqTerm (ne (ne _ _ _)) t≡u u≡v = trans t≡u u≡v
transEqTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext))
            (t≡u , ⊩t , ⊩u , [t≡u])
            (t≡u₁ , ⊩t₁ , ⊩u₁ , [t≡u]₁) =
  trans t≡u t≡u₁ , ⊩t , ⊩u₁
    , (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
                                ([t≡u] ρ ⊢Δ [a])
                                ([t≡u]₁ ρ ⊢Δ [a]))
transEqTerm (emb {l< = 0<1} x) t≡u u≡v = transEqTerm x t≡u u≡v
