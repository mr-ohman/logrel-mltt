module Definition.LogicalRelation.Properties where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


reflEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
  Π⁰[ F , G , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ U = PE.refl
reflEq ¹ (ℕ ⊢Γ) = id (ℕ ⊢Γ)
reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , id (Π ⊢F ▹ ⊢G) , refl (Π ⊢F ▹ ⊢G) , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ (emb x) = reflEq ⁰ x

symEq : ∀ {Γ A B} l l' ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l' ⟩ B) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l' ⟩ B ≡ A / [B]
symEq ⁰ ⁰ (ℕ D) (ℕ D₁) A≡B = red D
symEq ⁰ ⁰ (ℕ D) (ne D₁ neK) A≡B = {!!}
symEq ⁰ ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B = {!!}

symEq ⁰ ⁰ (ne D neK) (ℕ D₁) A≡B = {!!}
symEq ⁰ ⁰ (ne D neK) (ne D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
symEq ⁰ ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) A≡B = {!!}

symEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) A≡B = {!!}
symEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) A≡B = {!!}
symEq ⁰ ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = Π⁰[ _ , _ , red D , sym A≡B , {!!} , {!!} ]

symEq ⁰ ¹ (ℕ D) U A≡B = {!!}
symEq ⁰ ¹ (ℕ D) (ℕ ⊢Γ) A≡B = red D
symEq ⁰ ¹ (ℕ D) (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}

symEq ⁰ ¹ (ne D neK) U A≡B = {!!}
symEq ⁰ ¹ (ne D neK) (ℕ ⊢Γ) A≡B = {!!}
symEq ⁰ ¹ (ne D neK) (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}

symEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) U A≡B = {!!}
symEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ ⊢Γ) A≡B = {!!}
symEq ⁰ ¹ (Π D ⊢F ⊢G [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ [B] [F]₁ [G]₁ G-ext₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = Π¹[ _ , _ , red D , sym A≡B , {!!} , {!!} ]

symEq ⁰ ¹ [A] (emb x) A≡B = symEq ⁰ ⁰ [A] x A≡B

symEq ¹ ⁰ U (ℕ D) A≡B = {!!}
symEq ¹ ⁰ U (ne D neK) A≡B = {!!}
symEq ¹ ⁰ U (Π D ⊢F ⊢G [F] [G] G-ext) A≡B = {!!}

symEq ¹ ⁰ (ℕ ⊢Γ) (ℕ D) A≡B = {!!}
symEq ¹ ⁰ (ℕ ⊢Γ) (ne D neK) A≡B = {!!}
symEq ¹ ⁰ (ℕ ⊢Γ) (Π D ⊢F ⊢G [F] [G] G-ext) A≡B = {!!}

symEq ¹ ⁰ (Π ⊢F ⊢G [A] [F] [G] G-ext) (ℕ D) A≡B = {!!}
symEq ¹ ⁰ (Π ⊢F ⊢G [A] [F] [G] G-ext) (ne D neK) A≡B = {!!}
symEq ¹ ⁰ (Π ⊢F ⊢G [A] [F] [G] G-ext) (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] = Π⁰[ F' , G' , {!!} ⇨ D' , sym A≡B , {!!} , {!!} ]

symEq ¹ ⁰ (emb x) [B] A≡B = symEq ⁰ ⁰ x [B] A≡B

symEq ¹ ¹ U U A≡B = PE.refl
symEq ¹ ¹ U (ℕ ⊢Γ) A≡B = {!!}
symEq ¹ ¹ U (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}

symEq ¹ ¹ (ℕ ⊢Γ) U A≡B = {!!}
symEq ¹ ¹ (ℕ ⊢Γ) (ℕ ⊢Γ₁) A≡B = A≡B
symEq ¹ ¹ (ℕ ⊢Γ) (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}

symEq ¹ ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) U A≡B = {!!}
symEq ¹ ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) (ℕ ⊢Γ) A≡B = {!!}
symEq ¹ ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ [B] [F]₁ [G]₁ G-ext₁) A≡B = {!!}

symEq ¹ ¹ (emb x) [B] A≡B = symEq ⁰ ¹ x [B] A≡B
symEq ¹ ¹ [A] (emb x) A≡B = symEq ¹ ⁰ [A] x A≡B

-- symEq ⁰ (ℕ x) (ℕ x₁) A≡B = red x
-- symEq ⁰ (ℕ D) (ne D₁ neK) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , (ne neK))))
-- symEq ⁰ (ℕ x) (Π x₁ x₂ x₃ [F] [G] x₄) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red x₁ , Π)))

-- symEq ⁰ (ne x neK) (ℕ D) ne[ M , D' , neM , K≡M ] = ⊥-elim (ℕ≢ne neM (whrDet*' (red D , ℕ) (red D' , ne neM)))
-- symEq ⁰ (ne D neK) (ne D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
-- symEq ⁰ (ne x neK) (Π D ⊢F ⊢G [F] [G] G-ext) ne[ M , D' , neM , K≡M ] = ⊥-elim (Π≢ne neM (whrDet*' (red D , Π) (red D' , (ne neM))))

-- symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
--   ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
-- symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
--   ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , (ne neK))))
-- symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
--   Π⁰[ _ , _ , red D , sym A≡B , (λ ρ ⊢Δ → {![F≡F']!}) , {!!} ]

-- symEq ¹ U U A≡B = PE.refl
-- symEq ¹ U (ℕ ⊢Γ) A≡B = {!!}
-- symEq ¹ U (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}
-- symEq ¹ U (emb x) A≡B = {!!}

-- symEq ¹ (ℕ ⊢Γ) [B] A≡B = {!!}
-- symEq ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) [B] A≡B = {!!}
-- symEq ¹ (emb x) [B] A≡B = {!!}


mutual
  wk : ∀ {Γ Δ A} l → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wkₜ ρ A
  wk ⁰ ρ ⊢Δ (ℕ x) = ℕ (T.wkRed:*: ρ ⊢Δ x)
  wk ⁰ ρ ⊢Δ (ne x x₁) = ne (T.wkRed:*: ρ ⊢Δ x) (wkNeutral (toWk ρ) x₁)
  wk {Γ} {Δ} ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] G-ext) =
    let y = T.wk ρ ⊢Δ x₁
        [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩⁰ wkₜ η (wkₜ η′ F)
        [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
        [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⁰ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⁰ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
        [a]' η η′ ⊢E [a] = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
        [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩⁰ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩⁰ wkLiftₜ (η •ₜ η′) G [ a ]
        [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
    in  Π (T.wkRed:*: ρ ⊢Δ x) y (T.wk (lift ρ) (⊢Δ ∙ y) x₂)
          (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
          (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
          (λ ρ₁ ⊢Δ₁ [a] x₄ → proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩⁰ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) (proof-irrelevanceEqTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄)))
  wk ¹ ρ ⊢Δ U = U
  wk ¹ ρ ⊢Δ (ℕ ⊢Γ) = (ℕ ⊢Δ)
  wk {Γ} {Δ} ¹ ρ ⊢Δ (Π {F} {G} ⊢F ⊢G A [F] [G] G-ext) =
    let y = T.wk ρ ⊢Δ ⊢F
        [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) → E ⊩¹ wkₜ η (wkₜ η′ F)
        [F]' η η′ ⊢E = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm η η′) ([F] (η •ₜ η′) ⊢E)
        [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩¹ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩¹ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
        [a]' η η′ ⊢E [a] = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm η η′)) ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
        [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E) ([a] : E ⊩¹ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E) → E ⊩¹ wkLiftₜ (η •ₜ η′) G [ a ]
        [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
    in  Π y (T.wk (lift ρ) (⊢Δ ∙ y) ⊢G) ([F] ρ ⊢Δ)
          (λ ρ₁ ⊢Δ₁ → PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
          (λ ρ₁ ⊢Δ₁ [a] → PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]))
          (λ ρ₁ ⊢Δ₁ [a] x₄ → proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a]) (PE.subst (λ z → _ ⊩¹ z) (wk-comp-comm-subst ρ₁ ρ G) ([G]' ρ₁ ρ ⊢Δ₁ [a])) (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁ ([a]' ρ₁ ρ ⊢Δ₁ [a]) (proof-irrelevanceEqTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) ([F]' ρ₁ ρ ⊢Δ₁) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) x₄)))
  wk ¹ ρ ⊢Δ (emb x) = emb (wk ⁰ ρ ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ A ≡ wkₜ ρ B / wk l ρ ⊢Δ [A]
  wkEq ⁰ ρ ⊢Δ (ℕ x) A≡B = T.wkRed* ρ ⊢Δ A≡B
  wkEq ⁰ ρ ⊢Δ (ne x x₁) ne[ M , D' , neM , K≡M ] = ne[ wkₜ ρ M , T.wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
  wkEq ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) Π⁰[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π⁰[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
      , (λ ρ₁ ⊢Δ₁ → proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩⁰ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
      , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩⁰ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
                        in  proof-irrelevanceEq'' ⁰ ⁰ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
  wkEq ¹ ρ ⊢Δ U A≡B = PE.cong (wkₜ ρ) A≡B
  wkEq ¹ ρ ⊢Δ (ℕ ⊢Γ) A≡B = wkRed* ρ ⊢Δ A≡B
  wkEq ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
    Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B
      , (λ ρ₁ ⊢Δ₁ → proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm ρ₁ ρ) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) (PE.subst (λ x₄ → _ ⊩¹ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
      , (λ ρ₁ ⊢Δ₁ [a] → let [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) (PE.subst (λ x₄ → _ ⊩¹ x₄) (wk-comp-comm ρ₁ ρ) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)) ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
                        in  proof-irrelevanceEq'' ¹ ¹ (wk-comp-comm-subst ρ₁ ρ G) (wk-comp-comm-subst ρ₁ ρ G') ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]') (PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')) ]
  wkEq ¹ ρ ⊢Δ (emb x) A≡B = wkEq ⁰ ρ ⊢Δ x A≡B

  wkTerm : ∀ {Γ Δ A t} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A]
         → Δ ⊩⟨ l ⟩ wkₜ ρ t ∷ wkₜ ρ A / wk l ρ ⊢Δ [A]
  wkTerm ⁰ ρ ⊢Δ (ℕ x) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ⁰ ρ ⊢Δ (ne x x₁) t₁ = T.wkTerm ρ ⊢Δ t₁
  wkTerm ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = T.wkTerm ρ ⊢Δ proj₁ ,
    (λ ρ₁ ⊢Δ₁ [a] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                            [F]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) [F]₁
                            [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                            [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                            [G]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                        in  proof-irrelevanceEqTerm'' ⁰ ⁰ (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (proj₂ (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' (proof-irrelevanceEqTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
  wkTerm ¹ ρ ⊢Δ U (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (wk ⁰ ρ ⊢Δ proj₂)
  wkTerm ¹ ρ ⊢Δ (ℕ ⊢Γ) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) (proj₁ , proj₂) = T.wkTerm ρ ⊢Δ proj₁ ,
    (λ ρ₁ ⊢Δ₁ [a] a≡b → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                            [F]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) [F]₁
                            [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                            [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                            [G]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                        in  proof-irrelevanceEqTerm'' ¹ ¹ (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ (proj₂ (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' (proof-irrelevanceEqTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ a≡b)))
  wkTerm ¹ ρ ⊢Δ (emb x) t₁ = wkTerm ⁰ ρ ⊢Δ x t₁

  wkEqTerm : ∀ {Γ Δ A t u} l → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
         → Δ ⊩⟨ l ⟩ wkₜ ρ t ≡ wkₜ ρ u ∷ wkₜ ρ A / wk l ρ ⊢Δ [A]
  wkEqTerm ⁰ ρ ⊢Δ (ℕ x) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] =
    ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ⁰ ρ ⊢Δ (ne x x₁) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
  wkEqTerm ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A] = Π x x₁ x₂ [F] [G] x₃
    in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ⁰ ρ ⊢Δ [A] ⊩t , wkTerm ⁰ ρ ⊢Δ [A] ⊩u ,
        (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                            [F]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm ρ₁ ρ) [F]₁
                            [a]' = proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                            [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                            [G]₂ = PE.subst (λ y → _ ⊩⁰ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                        in  proof-irrelevanceEqTerm'' ⁰ ⁰ (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (proof-irrelevanceTerm' ⁰ ⁰ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
  wkEqTerm ¹ ρ ⊢Δ U U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ⁰ ρ ⊢Δ ⊩t , wk ⁰ ρ ⊢Δ ⊩u , wkEq ⁰ ρ ⊢Δ ⊩t [t≡u] ]
  wkEqTerm ¹ ρ ⊢Δ (ℕ ⊢Γ) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ¹ ρ ⊢Δ (Π {F} {G} x x₁ [A] [F] [G] x₂) (t≡u , ⊩t , ⊩u , [t≡u]) =
    let [A] = Π x x₁ [A] [F] [G] x₂
    in  T.wkEqTerm ρ ⊢Δ t≡u , wkTerm ¹ ρ ⊢Δ [A] ⊩t , wkTerm ¹ ρ ⊢Δ [A] ⊩u ,
        (λ ρ₁ ⊢Δ₁ [a] → let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
                            [F]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm ρ₁ ρ) [F]₁
                            [a]' = proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
                            [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
                            [G]₂ = PE.subst (λ y → _ ⊩¹ y) (wk-comp-comm-subst ρ₁ ρ G) [G]₁
                        in  proof-irrelevanceEqTerm'' ¹ ¹ (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ)) (wk-comp-comm-subst ρ₁ ρ G) [G]₁ [G]₂ ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ (proof-irrelevanceTerm' ¹ ¹ (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a])))
  wkEqTerm ¹ ρ ⊢Δ (emb x) t≡u = wkEqTerm ⁰ ρ ⊢Δ x t≡u
