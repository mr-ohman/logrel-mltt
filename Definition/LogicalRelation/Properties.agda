module Definition.LogicalRelation.Properties where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


reflEq : ∀ {Γ A} T ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ A / [A]
reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
  let ⊩A = Π [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext
  in  Π⁰[ F , G , D , refl ⊢A , ⊩A , ⊩A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ U = PE.refl
reflEq ¹ ℕ = {!PE.refl!}
reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , {!PE.refl!} , PE.refl , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
reflEq ¹ (emb x) = reflEq ⁰ x

symEq : ∀ {Γ A B} T ([A] : Γ ⊩⟨ T ⟩ A) ([B] : Γ ⊩⟨ T ⟩ B) → Γ ⊩⟨ T ⟩ A ≡ B / [A] → Γ ⊩⟨ T ⟩ B ≡ A / [B]
symEq ⁰ (ℕ x) (ℕ x₁) A≡B = red x
symEq ⁰ (ℕ D) (ne D₁ neK) A≡B = ⊥-elim (ℕ≢ne neK (whrDet*' (A≡B , ℕ) (red D₁ , (ne neK))))
symEq ⁰ (ℕ x) (Π x₁ x₂ x₃ [F] [G] x₄) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (A≡B , ℕ) (red x₁ , Π)))

symEq ⁰ (ne x neK) (ℕ D) ne[ M , D' , neM , K≡M ] = ⊥-elim (ℕ≢ne neM (whrDet*' (red D , ℕ) (red D' , ne neM)))
symEq ⁰ (ne D neK) (ne D₁ neK₁) ne[ M , D' , neM , K≡M ] = ne[ _ , D , neK , trans (sym (subset* (red D₁))) (trans (subset* (red D')) (sym K≡M)) ]
symEq ⁰ (ne x neK) (Π D ⊢F ⊢G [F] [G] G-ext) ne[ M , D' , neM , K≡M ] = ⊥-elim (Π≢ne neM (whrDet*' (red D , Π) (red D' , (ne neM))))

symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (D' , Π)))
symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
  ⊥-elim (Π≢ne neK (whrDet*' (D' , Π) (red D₁ , (ne neK))))
symEq ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
  Π⁰[ _ , _ , red D , sym A≡B , ⊩B , ⊩A
    , (λ ρ ⊢Δ → {![F≡F']!}) , {!!} ]

symEq ¹ U U A≡B = PE.refl
symEq ¹ U ℕ A≡B = {!!}
symEq ¹ U (Π ⊢F ⊢G [B] [F] [G] G-ext) A≡B = {!!}
symEq ¹ U (emb x) A≡B = {!!}

symEq ¹ ℕ [B] A≡B = {!!}
symEq ¹ (Π ⊢F ⊢G [A] [F] [G] G-ext) [B] A≡B = {!!}
symEq ¹ (emb x) [B] A≡B = {!!}


mutual
  proof-irrelevanceEq : ∀ {Γ A B} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                      → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l' ⟩ A ≡ B / q
  proof-irrelevanceEq = {!!}

  proof-irrelevanceTerm : ∀ {Γ A t} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                        → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l' ⟩ t ∷ A / q
  proof-irrelevanceTerm = {!!}

  proof-irrelevanceEqTerm : ∀ {Γ A t u} l l' (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l' ⟩ A)
                          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l' ⟩ t ≡ u ∷ A / q
  proof-irrelevanceEqTerm = {!!}

  -- proof-irrelevanceEq' : ∀ {Γ A A' B} T (eq : A PE.≡ A') (p : Γ ⊩⟨ T ⟩ A) (q : Γ ⊩⟨ T ⟩ A') → Γ ⊩⟨ T ⟩ A ≡ B / p → Γ ⊩⟨ T ⟩ A' ≡ B / q
  -- proof-irrelevanceEq' T PE.refl p q A≡B = proof-irrelevanceEq T p q A≡B


  -- proof-irrelevanceEq : ∀ {Γ A B} T (p q : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / p → Γ ⊩⟨ T ⟩ A ≡ B / q
  -- proof-irrelevanceEq ⁰ (ℕ x) (ℕ x₁) A≡B = A≡B
  -- proof-irrelevanceEq ⁰ (ℕ x) (ne x₁ x₂) A≡B = ⊥-elim (ℕ≢ne x₂ (whrDet*' (red x , ℕ) (red x₁ , (ne x₂))))
  -- proof-irrelevanceEq ⁰ (ℕ x) (Π x₁ x₂ x₃ [F] [G] x₄) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (red x , ℕ) (red x₁ , Π)))

  -- proof-irrelevanceEq ⁰ (ne x x₁) (ℕ x₃) A≡B = ⊥-elim (ℕ≢ne x₁ (whrDet*' (red x₃ , ℕ) (red x , ne x₁)))
  -- proof-irrelevanceEq ⁰ (ne x x₁) (ne x₃ x₄) ne[ M , D' , neM , K≡M ] = ne[ M , D' , neM , trans (sym (subset* (red x₃))) (trans (subset* (red x)) K≡M) ]
  -- proof-irrelevanceEq ⁰ (ne x x₁) (Π x₃ x₄ x₅ [F] [G] x₆) A≡B = ⊥-elim (Π≢ne x₁ (whrDet*' (red x₃ , Π) (red x , (ne x₁))))

  -- proof-irrelevanceEq ⁰ (Π x x₁ x₂ [F] [G] x₃) (ℕ x₄) A≡B = ⊥-elim (ℕ≢Π (whrDet*' (red x₄ , ℕ) (red x , Π)))
  -- proof-irrelevanceEq ⁰ (Π x x₁ x₂ [F] [G] x₃) (ne x₄ x₅) A≡B = ⊥-elim (Π≢ne x₅ (whrDet*' (red x , Π) (red x₄ , (ne x₅))))
  -- proof-irrelevanceEq ⁰ (Π x x₁ x₂ [F] [G] x₃) (Π x₄ x₅ x₆ [F]₁ [G]₁ x₇) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
  --   let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red x , Π) (red x₄ , Π))
  --   in Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B
  --        , (λ ρ ⊢Δ → proof-irrelevanceEq' ⁰ (PE.cong (wkₜ ρ) F≡F₁) ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
  --        , ((λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm' ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
  --                          in  proof-irrelevanceEq' ⁰ (PE.cong (λ y → wkLiftₜ ρ y [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]))) ]

  -- proof-irrelevanceEq ¹ U U A≡B = A≡B
  -- proof-irrelevanceEq ¹ U (emb (ℕ x)) A≡B = ⊥-elim (U≢ℕ (whnfRed*' (red x) U))
  -- proof-irrelevanceEq ¹ U (emb (ne x x₁)) A≡B = ⊥-elim (U≢ne x₁ (whnfRed*' (red x) U))
  -- proof-irrelevanceEq ¹ U (emb (Π x x₁ x₂ [F] [G] x₃)) A≡B = ⊥-elim (U≢Π (whnfRed*' (red x) U))

  -- proof-irrelevanceEq ¹ ℕ ℕ A≡B = A≡B
  -- proof-irrelevanceEq ¹ ℕ (emb x) A≡B = PE.subst (λ x₁ → _ ⊩⁰ ℕ ≡ x₁ / x) (PE.sym A≡B) (reflEq ⁰ x)

  -- proof-irrelevanceEq ¹ (Π x x₁ p [F] [G] x₂) (Π x₃ x₄ q [F]₁ [G]₁ x₅) Π¹[ F' , G' , ΠFG≡ΠF'G' , t≡ΠF'G' , [F≡F'] , [G≡G'] ] =
  --   Π¹[ F' , G' , ΠFG≡ΠF'G' , t≡ΠF'G'
  --     , ((λ ρ ⊢Δ → proof-irrelevanceEq ¹ ([F] ρ ⊢Δ) ([F]₁ ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)))
  --     , ((λ ρ ⊢Δ [a]₁ → let [a] = proof-irrelevanceTerm ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
  --                       in  proof-irrelevanceEq ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]))) ]
  -- proof-irrelevanceEq ¹ (Π x x₁ p [F] [G] x₂) (emb x₃) Π¹[ F' , G' , ΠFG≡ΠF'G' , t≡ΠF'G' , [F≡F'] , [G≡G'] ] =
  --   PE.subst (λ x₁ → _ ⊩⁰ _ ≡ x₁ / x₃) (PE.trans ΠFG≡ΠF'G' (PE.sym t≡ΠF'G')) (reflEq ⁰ x₃)

  -- proof-irrelevanceEq ¹ (emb (ℕ x)) U A≡B = ⊥-elim (U≢ℕ (whnfRed*' (red x) U))
  -- proof-irrelevanceEq ¹ (emb (ne x x₁)) U A≡B = ⊥-elim (U≢ne x₁ (whnfRed*' (red x) U))
  -- proof-irrelevanceEq ¹ (emb (Π x x₁ x₂ [F] [G] x₃)) U A≡B = ⊥-elim (U≢Π (whnfRed*' (red x) U))

  -- proof-irrelevanceEq ¹ (emb (ℕ x)) ℕ A≡B = {!!}
  -- proof-irrelevanceEq ¹ (emb (ne x x₁)) ℕ A≡B = ⊥-elim (ℕ≢ne x₁ (whnfRed*' (red x) ℕ))
  -- proof-irrelevanceEq ¹ (emb (Π x x₁ x₂ [F] [G] x₃)) ℕ A≡B = ⊥-elim (ℕ≢Π (whnfRed*' (red x) ℕ))

  -- proof-irrelevanceEq ¹ (emb (ℕ x)) (Π x₁ x₂ q [F] [G] x₃) A≡B = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red x) Π)))
  -- proof-irrelevanceEq ¹ (emb (ne x₂ x)) (Π x₃ x₄ q [F] [G] x₅) A≡B = ⊥-elim (Π≢ne x (whnfRed*' (red x₂) Π))
  -- proof-irrelevanceEq ¹ (emb (Π x₃ x x₁ [F] [G] x₂)) (Π x₄ x₅ q [F]₁ [G]₁ x₆) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
  --   Π¹[ _ , _ , PE.refl , {!!} , (λ ρ ⊢Δ → reflEq ¹ ([F]₁ ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G]₁ ρ ⊢Δ [a])) ]

  -- proof-irrelevanceEq ¹ (emb x) (emb x₁) A≡B = proof-irrelevanceEq ⁰ x x₁ A≡B


  -- proof-irrelevanceTerm' : ∀ {Γ A A' t} T (eq : A PE.≡ A') (p : Γ ⊩⟨ T ⟩ A) (q : Γ ⊩⟨ T ⟩ A') → Γ ⊩⟨ T ⟩ t ∷ A / p → Γ ⊩⟨ T ⟩ t ∷ A' / q
  -- proof-irrelevanceTerm' T PE.refl p q t = proof-irrelevanceTerm T p q t

  -- proof-irrelevanceTerm : ∀ {Γ A t} T (p q : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ∷ A / p → Γ ⊩⟨ T ⟩ t ∷ A / q
  -- proof-irrelevanceTerm ⁰ (ℕ x) (ℕ x₁) t₁ = t₁
  -- proof-irrelevanceTerm ⁰ (ℕ x) (ne x₁ neK) t₁ = ⊥-elim (ℕ≢ne neK (whrDet*' (red x , ℕ) (red x₁ , (ne neK))))
  -- proof-irrelevanceTerm ⁰ (ℕ x) (Π x₁ x₂ x₃ [F] [G] x₄) t₁ = ⊥-elim (ℕ≢Π (whrDet*' (red x , ℕ) (red x₁ , Π)))

  -- proof-irrelevanceTerm ⁰ (ne x neK) (ℕ x₁) t₁ = ⊥-elim (ℕ≢ne neK (whrDet*' (red x₁ , ℕ) (red x , ne neK)))
  -- proof-irrelevanceTerm ⁰ (ne x neK) (ne x₁ neK₁) t₁ = t₁
  -- proof-irrelevanceTerm ⁰ (ne x neK) (Π x₁ x₂ x₃ [F] [G] x₄) t₁ = ⊥-elim (Π≢ne neK (whrDet*' (red x₁ , Π) (red x , (ne neK))))

  -- proof-irrelevanceTerm ⁰ (Π x x₁ x₂ [F] [G] x₃) (ℕ x₄) t₁ = ⊥-elim (ℕ≢Π (whrDet*' (red x₄ , ℕ) (red x , Π)))
  -- proof-irrelevanceTerm ⁰ (Π x x₁ x₂ [F] [G] x₃) (ne x₄ neK) t₁ = ⊥-elim (Π≢ne neK (whrDet*' (red x , Π) (red x₄ , (ne neK))))
  -- proof-irrelevanceTerm ⁰ (Π x x₁ x₂ [F] [G] x₃) (Π x₄ x₅ x₆ [F]₁ [G]₁ x₇) (proj₁ , proj₂) =
  --   proj₁ , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let F≡F₁ , G≡G₁ = Π-PE-injectivity (whrDet*' (red x , Π) (red x₄ , Π))
  --                                     [a]         = proof-irrelevanceTerm' ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
  --                                     [a≡b]       = proof-irrelevanceEqTerm' ⁰ (PE.cong (wkₜ ρ) (PE.sym F≡F₁)) ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
  --                                 in proof-irrelevanceEqTerm' ⁰ (PE.cong (λ G → wkLiftₜ ρ G [ _ ]) G≡G₁) ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) (proj₂ ρ ⊢Δ [a] [a≡b]))

  -- proof-irrelevanceTerm ¹ U U t = t
  -- proof-irrelevanceTerm ¹ U (emb (ℕ x)) t₁ = ⊥-elim (U≢ℕ (whnfRed*' (red x) U))
  -- proof-irrelevanceTerm ¹ U (emb (ne x neK)) t₁ = ⊥-elim (U≢ne neK (whnfRed*' (red x) U))
  -- proof-irrelevanceTerm ¹ U (emb (Π x x₁ x₂ [F] [G] x₃)) t₁ = ⊥-elim (U≢Π (whnfRed*' (red x) U))

  -- proof-irrelevanceTerm ¹ ℕ ℕ t = t
  -- proof-irrelevanceTerm ¹ ℕ (emb (ℕ D)) t = t
  -- proof-irrelevanceTerm ¹ ℕ (emb (ne D neK)) t₁ = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  -- proof-irrelevanceTerm ¹ ℕ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) t₁ = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  -- proof-irrelevanceTerm ¹ (Π x x₁ p [F] [G] x₂) (Π x₃ x₄ q [F]₁ [G]₁ x₅) (proj₁ , proj₂) =
  --   proj₁ , (λ ρ ⊢Δ [a]₁ [a≡b]₁ → let [a]   = proof-irrelevanceTerm ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a]₁
  --                                     [a≡b] = proof-irrelevanceEqTerm ¹ ([F]₁ ρ ⊢Δ) ([F] ρ ⊢Δ) [a≡b]₁
  --                                 in  proof-irrelevanceEqTerm ¹ ([G] ρ ⊢Δ [a]) ([G]₁ ρ ⊢Δ [a]₁) (proj₂ ρ ⊢Δ [a] [a≡b]))

  -- proof-irrelevanceTerm ¹ (Π x x₁ p [F] [G] x₂) (emb (ℕ D)) t₁ = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  -- proof-irrelevanceTerm ¹ (Π x x₁ p [F] [G] x₂) (emb (ne D neK)) t₁ = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  -- proof-irrelevanceTerm ¹ (Π x x₁ p [F] [G] x₂) (emb (Π D ⊢F ⊢G [F]₁ [G]₁ G-ext)) (proj₁ , proj₂) =
  --   proj₁ , (λ ρ ⊢Δ [a] [a≡b] → {!!})

  -- proof-irrelevanceTerm ¹ (emb (ℕ D)) U t₁ = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  -- proof-irrelevanceTerm ¹ (emb (ne D neK)) U t₁ = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  -- proof-irrelevanceTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) U t₁ = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  -- proof-irrelevanceTerm ¹ (emb (ℕ D)) ℕ t₁ = t₁
  -- proof-irrelevanceTerm ¹ (emb (ne D neK)) ℕ t₁ = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  -- proof-irrelevanceTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) ℕ t₁ = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  -- proof-irrelevanceTerm ¹ (emb (ℕ D)) (Π ⊢F ⊢G q [F] [G] G-ext) t₁ = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  -- proof-irrelevanceTerm ¹ (emb (ne D neK)) (Π ⊢F ⊢G q [F] [G] G-ext) t₁ = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  -- proof-irrelevanceTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) (proj₁ , proj₂) = proj₁ , {!!}

  -- proof-irrelevanceTerm ¹ (emb x) (emb x₁) t₁ = proof-irrelevanceTerm ⁰ x x₁ t₁

  -- proof-irrelevanceEqTerm' : ∀ {Γ A A' t u} T (eq : A PE.≡ A') (p : Γ ⊩⟨ T ⟩ A) (q : Γ ⊩⟨ T ⟩ A') → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ T ⟩ t ≡ u ∷ A' / q
  -- proof-irrelevanceEqTerm' T PE.refl p q t≡u = proof-irrelevanceEqTerm T p q t≡u

  -- proof-irrelevanceEqTerm : ∀ {Γ A t u} T (p q : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / q
  -- proof-irrelevanceEqTerm ⁰ (ℕ D) (ℕ D₁) t≡u = t≡u
  -- proof-irrelevanceEqTerm ⁰ (ℕ D) (ne D₁ neK) t≡u = ⊥-elim (ℕ≢ne neK (whrDet*' (red D , ℕ) (red D₁ , (ne neK))))
  -- proof-irrelevanceEqTerm ⁰ (ℕ D) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (whrDet*' (red D , ℕ) (red D₁ , Π)))

  -- proof-irrelevanceEqTerm ⁰ (ne D neK) (ℕ D₁) t≡u = ⊥-elim (ℕ≢ne neK (whrDet*' (red D₁ , ℕ) (red D , ne neK)))
  -- proof-irrelevanceEqTerm ⁰ (ne D neK) (ne D₁ neK₁) t≡u = t≡u
  -- proof-irrelevanceEqTerm ⁰ (ne D neK) (Π D₁ ⊢F ⊢G [F] [G] G-ext) t≡u = ⊥-elim (Π≢ne neK (whrDet*' (red D₁ , Π) (red D , (ne neK))))

  -- proof-irrelevanceEqTerm ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ℕ D₁) t≡u = ⊥-elim (ℕ≢Π (whrDet*' (red D₁ , ℕ) (red D , Π)))
  -- proof-irrelevanceEqTerm ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (ne D₁ neK) t≡u = ⊥-elim (Π≢ne neK (whrDet*' (red D , Π) (red D₁ , (ne neK))))
  -- proof-irrelevanceEqTerm ⁰ (Π D ⊢F ⊢G [F] [G] G-ext) (Π D₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁) t≡u = {!!}

  -- proof-irrelevanceEqTerm ¹ U U t≡u = t≡u
  -- proof-irrelevanceEqTerm ¹ U (emb (ℕ D)) t≡u = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  -- proof-irrelevanceEqTerm ¹ U (emb (ne D neK)) t≡u = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  -- proof-irrelevanceEqTerm ¹ U (emb (Π D ⊢F ⊢G [F] [G] G-ext)) t≡u = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  -- proof-irrelevanceEqTerm ¹ ℕ ℕ t≡u = t≡u
  -- proof-irrelevanceEqTerm ¹ ℕ (emb (ℕ D)) t≡u = t≡u
  -- proof-irrelevanceEqTerm ¹ ℕ (emb (ne D neK)) t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  -- proof-irrelevanceEqTerm ¹ ℕ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  -- proof-irrelevanceEqTerm ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) t≡u = {!!}
  -- proof-irrelevanceEqTerm ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (emb (ℕ D)) t≡u = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  -- proof-irrelevanceEqTerm ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (emb (ne D neK)) t≡u = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  -- proof-irrelevanceEqTerm ¹ (Π ⊢F ⊢G p [F] [G] G-ext) (emb (Π D ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁)) t≡u = {!!}

  -- proof-irrelevanceEqTerm ¹ (emb (ℕ D)) U t≡u = ⊥-elim (U≢ℕ (whnfRed*' (red D) U))
  -- proof-irrelevanceEqTerm ¹ (emb (ne D neK)) U t≡u = ⊥-elim (U≢ne neK (whnfRed*' (red D) U))
  -- proof-irrelevanceEqTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) U t≡u = ⊥-elim (U≢Π (whnfRed*' (red D) U))

  -- proof-irrelevanceEqTerm ¹ (emb (ℕ D)) ℕ t≡u = t≡u
  -- proof-irrelevanceEqTerm ¹ (emb (ne D neK)) ℕ t≡u = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
  -- proof-irrelevanceEqTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) ℕ t≡u = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))

  -- proof-irrelevanceEqTerm ¹ (emb (ℕ D)) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
  -- proof-irrelevanceEqTerm ¹ (emb (ne D neK)) (Π ⊢F ⊢G q [F] [G] G-ext) t≡u = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
  -- proof-irrelevanceEqTerm ¹ (emb (Π D ⊢F ⊢G [F] [G] G-ext)) (Π ⊢F₁ ⊢G₁ q [F]₁ [G]₁ G-ext₁) t≡u = {!!}

  -- proof-irrelevanceEqTerm ¹ (emb x) (emb x₁) t≡u = proof-irrelevanceEqTerm ⁰ x x₁ t≡u


mutual
  wk : ∀ {Γ Δ A} T → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ T ⟩ A → Δ ⊩⟨ T ⟩ U.wkₜ ρ A
  wk ⁰ ρ ⊢Δ (ℕ x) = ℕ (T.wkRed:*: ρ ⊢Δ x)
  wk ⁰ ρ ⊢Δ (ne x x₁) = ne (T.wkRed:*: ρ ⊢Δ x) (wkNeutral (toWk ρ) x₁)
  wk ⁰ ρ ⊢Δ (Π {F} {G} x x₁ x₂ [F] [G] x₃) =
    let y = T.wk ρ ⊢Δ x₁
    in Π (T.wkRed:*: ρ ⊢Δ x) y (T.wk (lift ρ) (⊢Δ ∙ y) x₂)
         (λ ρ₁ ⊢Δ₁ → wk ⁰ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) {!!} {!!}
  wk ¹ ρ ⊢Δ U = U
  wk ¹ ρ ⊢Δ ℕ = ℕ
  wk ¹ ρ ⊢Δ (Π F G A [F] [G] G-ext) = let y = T.wk ρ ⊢Δ F in Π y (T.wk (lift ρ) (⊢Δ ∙ y) G) ([F] ρ ⊢Δ) (λ ρ₁ ⊢Δ₁ → wk ¹ ρ₁ ⊢Δ₁ ([F] ρ ⊢Δ)) {!!} {!!}
  wk ¹ ρ ⊢Δ (emb x) = emb (wk ⁰ ρ ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ A ≡ B / [A]
       → Δ ⊩⟨ T ⟩ U.wkₜ ρ A ≡ U.wkₜ ρ B / wk T ρ ⊢Δ [A]
  wkEq ⁰ ρ ⊢Δ (ℕ x) A≡B = T.wkRed* ρ ⊢Δ A≡B
  wkEq ⁰ ρ ⊢Δ (ne x x₁) ne[ M , D' , neM , K≡M ] = ne[ wkₜ ρ M , T.wkRed:*: ρ ⊢Δ D' , wkNeutral (toWk ρ) neM , T.wkEq ρ ⊢Δ K≡M ]
  wkEq ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) Π⁰[ F' , G' , D' , A≡B , ⊩A , ⊩B , [F≡F'] , [G≡G'] ] =
    Π⁰[ wkₜ ρ F' , wkLiftₜ ρ G' , T.wkRed* ρ ⊢Δ D' , T.wkEq ρ ⊢Δ A≡B , wk ⁰ ρ ⊢Δ ⊩A , wk ⁰ ρ ⊢Δ ⊩B , {!!} , {!!} ]
  wkEq ¹ ρ ⊢Δ U A≡B = PE.cong (wkₜ ρ) A≡B
  wkEq ¹ ρ ⊢Δ ℕ A≡B = {!PE.cong (wkₜ ρ) A≡B!}
  wkEq ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) Π¹[ F' , G' , D' , ΠFG≡ΠF'G' , [F≡F'] , [G≡G'] ] =
    Π¹[ wkₜ ρ F' , wkLiftₜ ρ G' , {!!} , PE.cong (wkₜ ρ) ΠFG≡ΠF'G' , {!!} , {!!} ]
  wkEq ¹ ρ ⊢Δ (emb x) A≡B = wkEq ⁰ ρ ⊢Δ x A≡B

  wkTerm : ∀ {Γ Δ A t} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ∷ A / [A]
         → Δ ⊩⟨ T ⟩ U.wkₜ ρ t ∷ U.wkₜ ρ A / wk T ρ ⊢Δ [A]
  wkTerm ⁰ ρ ⊢Δ (ℕ x) ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ⁰ ρ ⊢Δ (ne x x₁) t₁ = T.wkTerm ρ ⊢Δ t₁
  wkTerm ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (λ ρ₁ ⊢Δ₁ [a] a≡b → {!!})
  wkTerm ¹ ρ ⊢Δ U (proj₁ , proj₂) = (T.wkTerm ρ ⊢Δ proj₁) , (wk ⁰ ρ ⊢Δ proj₂)
  wkTerm ¹ ρ ⊢Δ ℕ ℕ[ n , d , natN ] = ℕ[ wkₜ ρ n , T.wkRed:*:Term ρ ⊢Δ d , wkNatural (toWk ρ) natN ]
  wkTerm ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t₁ = {!!}
  wkTerm ¹ ρ ⊢Δ (emb x) t₁ = wkTerm ⁰ ρ ⊢Δ x t₁

  wkEqTerm : ∀ {Γ Δ A t u} T → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) ([A] : Γ ⊩⟨ T ⟩ A) → Γ ⊩⟨ T ⟩ t ≡ u ∷ A / [A]
         → Δ ⊩⟨ T ⟩ U.wkₜ ρ t ≡ U.wkₜ ρ u ∷ U.wkₜ ρ A / wk T ρ ⊢Δ [A]
  wkEqTerm ⁰ ρ ⊢Δ (ℕ x) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] =
    ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ⁰ ρ ⊢Δ (ne x x₁) t≡u = T.wkEqTerm ρ ⊢Δ t≡u
  wkEqTerm ⁰ ρ ⊢Δ (Π x x₁ x₂ [F] [G] x₃) t≡u = {!!}
  wkEqTerm ¹ ρ ⊢Δ U U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ T.wkTerm ρ ⊢Δ ⊢t , T.wkTerm ρ ⊢Δ ⊢u , T.wkEqTerm ρ ⊢Δ t≡u , wk ⁰ ρ ⊢Δ ⊩t , wk ⁰ ρ ⊢Δ ⊩u , wkEq ⁰ ρ ⊢Δ ⊩t [t≡u] ]
  wkEqTerm ¹ ρ ⊢Δ ℕ ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] ] = ℕ≡[ wkₜ ρ k , wkₜ ρ k' , T.wkRed*Term ρ ⊢Δ d , T.wkRed*Term ρ ⊢Δ d' , T.wkEqTerm ρ ⊢Δ t≡u , wk[Natural] (toWk ρ) (T.wkEqTerm ρ ⊢Δ) [k≡k'] ]
  wkEqTerm ¹ ρ ⊢Δ (Π x x₁ [A] [F] [G] x₂) t≡u = {!!}
  wkEqTerm ¹ ρ ⊢Δ (emb x) t≡u = wkEqTerm ⁰ ρ ⊢Δ x t≡u
