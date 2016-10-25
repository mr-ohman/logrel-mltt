module Definition.LogicalRelation.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic

open import Data.Product
open import Data.Unit
import Relation.Binary.PropositionalEquality as PE

mutual
  wkTermℕ : ∀ {Γ Δ A n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
          → ℕ[ Γ ] n ∷ A → ℕ[ Δ ] U.wk (toWk ρ) n ∷ U.wk (toWk ρ) A
  wkTermℕ ρ ⊢Δ ℕ[ n , d , natN , prop ] = ℕ[ U.wk (toWk ρ) n , wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN , wkNatural-prop ρ ⊢Δ natN prop ]

  wkNatural-prop : ∀ {Γ Δ n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) (natN : Natural n)
                 → natural-prop Γ n natN
                 → natural-prop Δ (wkₜ ρ n) (wkNatural (toWk ρ) natN)
  wkNatural-prop ρ ⊢Δ suc n = wkTermℕ ρ ⊢Δ n
  wkNatural-prop ρ ⊢Δ zero n = n
  wkNatural-prop ρ ⊢Δ (ne x) n = T.wkTerm ρ ⊢Δ n

mutual
  wkEqTermℕ : ∀ {Γ Δ A t u} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
            → ℕ[ Γ ] t ≡ u ∷ A
            → ℕ[ Δ ] U.wk (toWk ρ) t ≡ U.wk (toWk ρ) u ∷ U.wk (toWk ρ) A
  wkEqTermℕ ρ ⊢Δ ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] =
    ℕ≡[ U.wk (toWk ρ) k , U.wk (toWk ρ) k' , wkRed:*:Term ρ ⊢Δ d , wkRed:*:Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) [k≡k'] , wk[Natural]-prop ρ ⊢Δ [k≡k'] prop ]

  wk[Natural]-prop : ∀ {Γ Δ n n'} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([n≡n'] : [Natural] n n')
                   → [Natural]-prop Γ n n' [n≡n']
                   → [Natural]-prop Δ (U.wk (toWk ρ) n) (U.wk (toWk ρ) n') (wk[Natural] (toWk ρ) [n≡n'])
  wk[Natural]-prop ρ ⊢Δ suc [n≡n'] = wkEqTermℕ ρ ⊢Δ [n≡n']
  wk[Natural]-prop ρ ⊢Δ zero t = t
  wk[Natural]-prop ρ ⊢Δ (ne x x₁) n≡n' = T.wkEqTerm ρ ⊢Δ n≡n'

wk : ∀ {l Γ Δ A} → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wkₜ ρ A
wk ρ ⊢Δ (U (U l' l< ⊢Γ)) = U (U l' l< ⊢Δ)
wk ρ ⊢Δ (ℕ (ℕ D)) = ℕ (ℕ (wkRed:*: ρ ⊢Δ D))
wk ρ ⊢Δ (ne (ne K D neK)) = ne (ne (wkₜ ρ K) (wkRed:*: ρ ⊢Δ D) (wkNeutral (toWk ρ) neK))
wk {l} {Γ} {Δ} ρ ⊢Δ (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) =
  let y = T.wk ρ ⊢Δ ⊢F
      [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩⟨ l ⟩ wkₜ η (wkₜ η′ F)
      [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
      [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⟨ l ⟩ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
      [a]' η η′ ⊢E [a] = irrelevanceTerm' (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
      [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⟨ l ⟩ wkLiftₜ (η •ₜ η′) G [ a ]
      [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
  in  Π (Π (wkₜ ρ F) (wkLiftₜ ρ G) (T.wkRed:*: ρ ⊢Δ D) y (T.wk (lift ρ) (⊢Δ ∙ y) ⊢G)
        (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
        (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
        (λ ρ₁ ⊢Δ₁ [a] [b] x₄ → irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩⟨ l ⟩ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) ([a]' ρ₁ ρ ⊢Δ₁ [b]) (irrelevanceEqTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄))))
wk {⁰} ρ ⊢Δ (emb {l< = ()} x)
wk {¹} ρ ⊢Δ (emb {l< = 0<1} x) = emb {l< = 0<1} (wk ρ ⊢Δ x)

wkEq : ∀ {l Γ Δ A B} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A]
     → Δ ⊩⟨ l ⟩ wkₜ ρ A ≡ wkₜ ρ B / wk ρ ⊢Δ [A]
wkEq ρ ⊢Δ (U UA) PE.refl = PE.refl
wkEq ρ ⊢Δ (ℕ ℕA) A≡B = wkRed* ρ ⊢Δ A≡B
wkEq ρ ⊢Δ (ne neA) ne[ M , D' , neM , K≡M ] = ne[ U.wk (toWk ρ) M , wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
wkEq ρ ⊢Δ (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
    , (λ ρ₁ ⊢Δ₁ → irrelevanceEq'' (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩⟨ _ ⟩ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
    , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩⟨ _ ⟩ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
                      in  irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
wkEq {⁰} ρ ⊢Δ (emb {l< = ()} x) A≡B
wkEq {¹} ρ ⊢Δ (emb {l< = 0<1} x) A≡B = wkEq ρ ⊢Δ x A≡B

wkTerm : ∀ {l Γ Δ A t} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ t ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkTerm ρ ⊢Δ (U (U .⁰ 0<1 ⊢Γ)) (⊢t , ⊩t) = T.wkTerm ρ ⊢Δ ⊢t , wk ρ ⊢Δ ⊩t
wkTerm ρ ⊢Δ (ℕ ℕA) [t] = wkTermℕ ρ ⊢Δ [t]
wkTerm ρ ⊢Δ (ne neA) t = T.wkTerm ρ ⊢Δ t
wkTerm ρ ⊢Δ (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (⊢t , ⊩t , [t]₁) = T.wkTerm ρ ⊢Δ ⊢t ,
  (λ ρ₁ ⊢Δ₁ [a] [b] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                              [F]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm ρ₁ ρ) [F]₁
                              [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                              [b]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [b]
                              [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                              [G]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                          in  irrelevanceEqTerm'' (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (⊩t (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' [b]' (irrelevanceEqTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
  , (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                        [F]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm ρ₁ ρ) [F]₁
                        [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                        [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                        [G]₂ = PE.subst (λ y → _ ⊩⟨ _ ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                    in  irrelevanceTerm'' (wk-comp-comm-subst ρ₁ ρ G) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) [G]₁ [G]₂ ([t]₁ (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' ))
wkTerm ρ ⊢Δ (emb {l< = 0<1} x) t = wkTerm ρ ⊢Δ x t

wkEqTerm : ∀ {l Γ Δ A t u} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ t ≡ wkₜ ρ u ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkEqTerm ρ ⊢Δ (U (U .⁰ 0<1 ⊢Γ)) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ρ ⊢Δ ⊩t , wk ρ ⊢Δ ⊩u , wkEq ρ ⊢Δ ⊩t [t≡u] ]
wkEqTerm ρ ⊢Δ (ℕ ℕA) [t≡u] = wkEqTermℕ ρ ⊢Δ [t≡u]
wkEqTerm ρ ⊢Δ (ne neA) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
wkEqTerm {l} ρ ⊢Δ (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) (t≡u , ⊩t , ⊩u , [t≡u]) =
  let [A] = Π (Π F G D ⊢F ⊢G [F] [G] G-ext)
  in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ρ ⊢Δ [A] ⊩t , wkTerm ρ ⊢Δ [A] ⊩u ,
      (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                          [F]₂ = PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm ρ₁ ρ) [F]₁
                          [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                          [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                          [G]₂ = PE.subst (λ y → _ ⊩⟨ l ⟩ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                      in  irrelevanceEqTerm'' (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
wkEqTerm ρ ⊢Δ (emb {l< = 0<1} x) t≡u = wkEqTerm ρ ⊢Δ x t≡u
