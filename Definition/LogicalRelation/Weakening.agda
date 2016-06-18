module Definition.LogicalRelation.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Reflexivity
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic

open import Tools.Context

open import Data.Product
open import Data.Unit
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


wkNatural-prop : ∀ {Γ Δ n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) (natN : Natural n)
               → natural-prop Γ n natN
               → natural-prop Δ (wkₜ ρ n) (wkNatural (toWk ρ) natN)
wkNatural-prop ρ ⊢Δ (suc natN) (proj₁ , natProp) = wkNatural-prop ρ ⊢Δ natN proj₁ , T.wkTerm ρ ⊢Δ natProp
wkNatural-prop ρ ⊢Δ zero natProp = tt
wkNatural-prop ρ ⊢Δ (ne x) natProp = tt

wk[Natural]-prop : ∀ {Γ Δ m n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                   ([m≡n] : [Natural] (λ n n' → Γ ⊢ n ≡ n' ∷ ℕ) m n)
                   → naturalEq-prop Γ m n [m≡n]
                   → naturalEq-prop Δ (U.wk (toWk ρ) m) (U.wk (toWk ρ) n)
                     (wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [m≡n])
wk[Natural]-prop ρ ⊢Δ (suc [m≡n]) (proj₁ , proj₂) = wk[Natural]-prop ρ ⊢Δ [m≡n] proj₁ , T.wkEqTerm ρ ⊢Δ proj₂
wk[Natural]-prop ρ ⊢Δ zero prop = tt
wk[Natural]-prop ρ ⊢Δ (ne x x₁ x₂) prop = tt

wk : ∀ {l Γ Δ A} → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wkₜ ρ A
wk ρ ⊢Δ (U {l< = l<} ⊢Γ) = U {l< = l<} ⊢Δ
wk ρ ⊢Δ (ℕ D) = ℕ (wkRed:*: ρ ⊢Δ D)
wk ρ ⊢Δ (ne D neK) = ne (wkRed:*: ρ ⊢Δ D) (wkNeutral (toWk ρ) neK)
wk {l} {Γ} {Δ} ρ ⊢Δ (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) =
  let y = T.wk ρ ⊢Δ ⊢F
      [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩⟨ l ⟩ wkₜ η (wkₜ η′ F)
      [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
      [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⟨ l ⟩ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
      [a]' η η′ ⊢E [a] = proof-irrelevanceTerm' (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
      [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⟨ l ⟩ wkLiftₜ (η •ₜ η′) G [ a ]
      [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
  in  Π (T.wkRed:*: ρ ⊢Δ D) y (T.wk (lift ρ) (⊢Δ ∙ y) ⊢G)
        (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
        (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
        (λ ρ₁ ⊢Δ₁ [a] x₄ → proof-irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩⟨ l ⟩ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) (proof-irrelevanceEqTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄)))
wk {⁰} ρ ⊢Δ (emb {l< = ()} x)
wk {¹} ρ ⊢Δ (emb {l< = 0<1} x) = emb {l< = 0<1} (wk ρ ⊢Δ x)

wkEq : ∀ {l Γ Δ A B} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A]
     → Δ ⊩⟨ l ⟩ wkₜ ρ A ≡ wkₜ ρ B / wk ρ ⊢Δ [A]
wkEq ρ ⊢Δ (U ⊢Γ) PE.refl = PE.refl
wkEq ρ ⊢Δ (ℕ D) A≡B = wkRed* ρ ⊢Δ A≡B
wkEq ρ ⊢Δ (ne D neK) ne[ M , D' , neM , K≡M ] = ne[ U.wk (toWk ρ) M , wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
wkEq ρ ⊢Δ (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
    , (λ ρ₁ ⊢Δ₁ → proof-irrelevanceEq'' (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩⟨ _ ⟩ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
    , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = proof-irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩⟨ _ ⟩ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
                      in  proof-irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
wkEq {⁰} ρ ⊢Δ (emb {l< = ()} x) A≡B
wkEq {¹} ρ ⊢Δ (emb {l< = 0<1} x) A≡B = wkEq ρ ⊢Δ x A≡B

wkTerm : ∀ {l Γ Δ A t} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ t ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkTerm {⁰} ρ ⊢Δ (U {l< = ()} ⊢Γ) (⊢t , ⊩t)
wkTerm {¹} ρ ⊢Δ (U {l< = 0<1} ⊢Γ) (⊢t , ⊩t) = T.wkTerm ρ ⊢Δ ⊢t , wk ρ ⊢Δ ⊩t
wkTerm ρ ⊢Δ (ℕ D) ℕ[ n , d , natN , prop ] = ℕ[ U.wk (toWk ρ) n , wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN , wkNatural-prop ρ ⊢Δ natN prop ]
wkTerm ρ ⊢Δ (ne D neK) t = T.wkTerm ρ ⊢Δ t
wkTerm ρ ⊢Δ (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) (⊢t , ⊩t) = T.wkTerm ρ ⊢Δ ⊢t ,
  (λ ρ₁ ⊢Δ₁ [a] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                          [F]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm ρ₁ ρ) [F]₁
                          [a]' = proof-irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                          [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                          [G]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                      in  proof-irrelevanceEqTerm'' (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (⊩t (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' (proof-irrelevanceEqTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
wkTerm {⁰} ρ ⊢Δ (emb {l< = ()} x) t
wkTerm {¹} ρ ⊢Δ (emb {l< = 0<1} x) t = wkTerm ρ ⊢Δ x t

wkEqTerm : ∀ {l Γ Δ A t u} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ t ≡ wkₜ ρ u ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkEqTerm {⁰} ρ ⊢Δ (U {l< = ()} ⊢Γ)
wkEqTerm {¹} ρ ⊢Δ (U {l< = 0<1} ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ρ ⊢Δ ⊩t , wk ρ ⊢Δ ⊩u , wkEq ρ ⊢Δ ⊩t [t≡u] ]
wkEqTerm ρ ⊢Δ (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] =
  ℕ≡[ U.wk (toWk ρ) k , U.wk (toWk ρ) k' , wkRed*Term ρ ⊢Δ d , wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] , wk[Natural]-prop ρ ⊢Δ [k≡k'] prop ]
wkEqTerm ρ ⊢Δ (ne D neK) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
wkEqTerm {l} ρ ⊢Δ (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) (t≡u , ⊩t , ⊩u , [t≡u]) =
  let [A] = Π D ⊢F ⊢G [F] [G] G-ext
  in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ρ ⊢Δ [A] ⊩t , wkTerm ρ ⊢Δ [A] ⊩u ,
      (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                          [F]₂ = PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm ρ₁ ρ) [F]₁
                          [a]' = proof-irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                          [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                          [G]₂ = PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                      in  proof-irrelevanceEqTerm'' (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (proof-irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
wkEqTerm {⁰} ρ ⊢Δ (emb {l< = ()} x) t≡u
wkEqTerm {¹} ρ ⊢Δ (emb {l< = 0<1} x) t≡u = wkEqTerm ρ ⊢Δ x t≡u

-- mutual
--   wk : ∀ {Γ Δ A} l → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wkₜ ρ A
--   wk ⁰ ρ ⊢Δ (ℕ x) = ℕ (T.wkRed:*: ρ ⊢Δ x)
--   wk ⁰ ρ ⊢Δ (ne x x₁) = ne (T.wkRed:*: ρ ⊢Δ x) (wkNeutral (toWk ρ) x₁)
--   wk {Γ} {Δ} ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] G-ext) =
--     let y = T.wk ρ ⊢Δ x₁
--         [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩⁰ wkₜ η (wkₜ η′ F)
--         [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
--         [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⁰ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⁰ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
--         [a]' η η′ ⊢E [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
--         [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⁰ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⁰ wkLiftₜ (η •ₜ η′) G [ a ]
--         [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
--     in  Π (T.wkRed:*: ρ ⊢Δ x) y (T.wk (lift ρ) (⊢Δ ∙ y) x₂)
--           (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
--           (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
--           (λ ρ₁ ⊢Δ₁ [a] x₄ → proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩⁰ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) (proof-irrelevanceEqTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄)))
--   wk ¹ ρ ⊢Δ U = U
--   wk ¹ ρ ⊢Δ (ℕ ⊢Γ) = (ℕ ⊢Δ)
--   wk {Γ} {Δ} ¹ ρ ⊢Δ (Π {F} {G} ⊢F ⊢G A [F] [G] G-ext) =
--     let y = T.wk ρ ⊢Δ ⊢F
--         [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩¹ wkₜ η (wkₜ η′ F)
--         [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
--         [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩¹ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩¹ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
--         [a]' η η′ ⊢E [a] = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
--         [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩¹ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩¹ wkLiftₜ (η •ₜ η′) G [ a ]
--         [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
--     in  Π y (T.wk (lift ρ) (⊢Δ ∙ y) ⊢G) ([F] ρ ⊢Δ)
--           (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
--           (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
--           (λ ρ₁ ⊢Δ₁ [a] x₄ → proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩¹ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) (proof-irrelevanceEqTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄)))
--   wk ¹ ρ ⊢Δ (emb x) = emb (wk ⁰ ρ ⊢Δ x)

--   wkEq : ∀ {Γ Δ A B} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A]
--        → Δ ⊩⟨ l ⟩ wkₜ ρ A ≡ wkₜ ρ B / wk l ρ ⊢Δ [A]
--   wkEq ⁰ ρ ⊢Δ (ℕ x) A≡B = T.wkRed* ρ ⊢Δ A≡B
--   wkEq ⁰ ρ ⊢Δ (ne x x₁) ne[ M , D' , neM , K≡M ] = ne[ wkₜ ρ M , T.wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
--   wkEq ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
--     Π⁰[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
--       , (λ ρ₁ ⊢Δ₁ → proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩⁰ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
--       , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩⁰ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
--                         in  proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
--   wkEq ¹ ρ ⊢Δ U A≡B = PE.cong (wkₜ ρ) A≡B
--   wkEq ¹ ρ ⊢Δ (ℕ ⊢Γ) A≡B = wkRed* ρ ⊢Δ A≡B
--   wkEq ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
--     Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
--       , (λ ρ₁ ⊢Δ₁ → proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩¹ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
--       , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩¹ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
--                         in  proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
--   wkEq ¹ ρ ⊢Δ (emb x) A≡B = wkEq ⁰ ρ ⊢Δ x A≡B

--   wkTerm : ∀ {Γ Δ A t} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A]
--          → Δ ⊩⟨ l ⟩ wkₜ ρ t ∷ wkₜ ρ A / wk l ρ ⊢Δ [A]
--   wkTerm ⁰ ρ ⊢Δ (ℕ x) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
--   wkTerm ⁰ ρ ⊢Δ (ne x x₁) t₁ = T.wkTerm ρ ⊢Δ t₁
--   wkTerm ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = T.wkTerm ρ ⊢Δ proj₁ ,
--     (λ ρ₁ ⊢Δ₁ [a] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
--                             [F]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) [F]₁
--                             [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
--                             [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
--                             [G]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
--                         in  proof-irrelevanceEqTerm'' ⁰ ⁰ (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (proj₂ (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' (proof-irrelevanceEqTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
--   wkTerm ¹ ρ ⊢Δ U (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (wk ⁰ ρ ⊢Δ proj₂)
--   wkTerm ¹ ρ ⊢Δ (ℕ ⊢Γ) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
--   wkTerm ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) (proj₁ , proj₂) = T.wkTerm ρ ⊢Δ proj₁ ,
--     (λ ρ₁ ⊢Δ₁ [a] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
--                             [F]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) [F]₁
--                             [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
--                             [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
--                             [G]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
--                         in  proof-irrelevanceEqTerm'' ¹ ¹ (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (proj₂ (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' (proof-irrelevanceEqTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
--   wkTerm ¹ ρ ⊢Δ (emb x) t₁ = wkTerm ⁰ ρ ⊢Δ x t₁

--   wkEqTerm : ∀ {Γ Δ A t u} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
--          → Δ ⊩⟨ l ⟩ wkₜ ρ t ≡ wkₜ ρ u ∷ wkₜ ρ A / wk l ρ ⊢Δ [A]
--   wkEqTerm ⁰ ρ ⊢Δ (ℕ x) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] =
--     ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
--   wkEqTerm ⁰ ρ ⊢Δ (ne x x₁) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
--   wkEqTerm ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) (t≡u , ⊩t , ⊩u , [t≡u]) =
--     let [A] = Π x x₁ x₂ [F] [G] x₃
--     in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ⁰ ρ ⊢Δ [A] ⊩t , wkTerm ⁰ ρ ⊢Δ [A] ⊩u ,
--         (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
--                             [F]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) [F]₁
--                             [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
--                             [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
--                             [G]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
--                         in  proof-irrelevanceEqTerm'' ⁰ ⁰ (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
--   wkEqTerm ¹ ρ ⊢Δ U U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ⁰ ρ ⊢Δ ⊩t , wk ⁰ ρ ⊢Δ ⊩u , wkEq ⁰ ρ ⊢Δ ⊩t [t≡u] ]
--   wkEqTerm ¹ ρ ⊢Δ (ℕ ⊢Γ) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
--   wkEqTerm ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) (t≡u , ⊩t , ⊩u , [t≡u]) =
--     let [A] = Π x x₁ [A] [F] [G] x₂
--     in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ¹ ρ ⊢Δ [A] ⊩t , wkTerm ¹ ρ ⊢Δ [A] ⊩u ,
--         (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
--                             [F]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) [F]₁
--                             [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
--                             [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
--                             [G]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
--                         in  proof-irrelevanceEqTerm'' ¹ ¹ (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
--   wkEqTerm ¹ ρ ⊢Δ (emb x) t≡u = wkEqTerm ⁰ ρ ⊢Δ x t≡u
