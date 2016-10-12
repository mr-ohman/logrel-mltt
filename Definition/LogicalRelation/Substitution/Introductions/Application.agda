module Definition.LogicalRelation.Substitution.Introductions.Application where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Data.Empty
open import Data.Product

import Relation.Binary.PropositionalEquality as PE


appTerm : ∀ {F G t u Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ∷ G [ u ] / [G[u]]
appTerm [F] [G[u]] (ℕ D) [t] [u] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
appTerm [F] [G[u]] (ne D neK) [t] [u] = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
appTerm [F] [G[u]] (Π D ⊢F ⊢G [F'] [G'] G-ext) (_ , _ , [t]) [u] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' (PE.trans F≡F' (PE.sym (wk-id _ 0))) [F] ([F'] T.id ⊢Γ) [u]
  in  irrelevanceTerm'' (PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G')))
                        (PE.cong (λ x → x ∘ _) (wk-id _ 0))
                        ([G'] T.id ⊢Γ [u]') [G[u]] ([t] T.id ⊢Γ [u]')
appTerm [F] [G[u]] (emb {l< = 0<1} x) [t] [u] = appTerm [F] [G[u]] x [t] [u]

app-congTerm : ∀ {F G t t' u u' Γ l l'}
          ([F] : Γ ⊩⟨ l' ⟩ F)
          ([G[u]] : Γ ⊩⟨ l' ⟩ G [ u ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
          ([t≡t'] : Γ ⊩⟨ l ⟩ t ≡ t' ∷ Π F ▹ G / [ΠFG])
          ([u] : Γ ⊩⟨ l' ⟩ u ∷ F / [F])
          ([u'] : Γ ⊩⟨ l' ⟩ u' ∷ F / [F])
          ([u≡u'] : Γ ⊩⟨ l' ⟩ u ≡ u' ∷ F / [F])
        → Γ ⊩⟨ l' ⟩ t ∘ u ≡ t' ∘ u' ∷ G [ u ] / [G[u]]
app-congTerm [F] [G[u]] (ℕ D) [t≡t'] [u] [u'] [u≡u'] = ⊥-elim (ℕ≢Π (PE.sym (whnfRed*' (red D) Π)))
app-congTerm [F] [G[u]] (ne D neK) [t≡t'] [u] [u'] [u≡u'] = ⊥-elim (Π≢ne neK (whnfRed*' (red D) Π))
app-congTerm [F] [G[u]] (Π D ⊢F ⊢G [F]₁ [G] G-ext) (proj₁ , proj₂ , (proj₃ , proj₄ , proj₅) , proj₆) [u] [u'] [u≡u'] =
  let F≡F' , G≡G' = Π-PE-injectivity (whnfRed*' (red D) Π)
      F≡wkidF' = PE.trans F≡F' (PE.sym (wk-id _ 0))
      t∘x≡wkidt∘x : {a b : Term} → U.wk id a Term.∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a 0)
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ]) (PE.trans (wk-id _ 1) (PE.sym G≡G'))
      ⊢Γ = wf ⊢F
      [u]' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [u]
      [u']' = irrelevanceTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [u']
      [u≡u']' = irrelevanceEqTerm' F≡wkidF' [F] ([F]₁ T.id ⊢Γ) [u≡u']
      [tu≡t'u] = irrelevanceEqTerm'' t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                     ([G] T.id ⊢Γ [u]') [G[u]] (proj₆ T.id ⊢Γ [u]')
      [t'u≡t'u'] = irrelevanceEqTerm'' t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                       ([G] T.id ⊢Γ [u]') [G[u]] (proj₄ T.id ⊢Γ [u]' [u']' [u≡u']')
  in  transEqTerm [G[u]] [tu≡t'u] [t'u≡t'u']
app-congTerm [F] [G[u]] (emb {l< = 0<1} x) [t≡t'] [u] [u'] [u≡u'] = app-congTerm [F] [G[u]] x [t≡t'] [u] [u'] [u≡u']

appₛ : ∀ {F G t u Γ}
       ([Γ] : ⊩ₛ Γ)
       ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
       ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
       ([t] : Γ ⊩ₛ⟨ ¹ ⟩t t ∷ Π F ▹ G / [Γ] / [ΠFG])
       ([u] : Γ ⊩ₛ⟨ ¹ ⟩t u ∷ F / [Γ] / [F])
     → Γ ⊩ₛ⟨ ¹ ⟩t t ∘ u ∷ G [ u ] / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appₛ {F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      proj₁[F] = proj₁ ([F] ⊢Δ [σ])
      proj₁[ΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      proj₁[t] = proj₁ ([t] ⊢Δ [σ])
      proj₁[u] = proj₁ ([u] ⊢Δ [σ])
      proj₁[G[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      proj₁[G[u]]' = irrelevance' (singleSubstLift G u) proj₁[G[u]]
  in  irrelevanceTerm' (PE.sym (singleSubstLift G u)) proj₁[G[u]]' proj₁[G[u]] (appTerm proj₁[F] proj₁[G[u]]' proj₁[ΠFG] (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  ,   (λ [σ'] [σ≡σ'] →
         let proj₁[u'] = convTerm₂ proj₁[F] (proj₁ ([F] ⊢Δ [σ'])) (proj₂ ([F] ⊢Δ [σ]) [σ'] [σ≡σ']) (proj₁ ([u] ⊢Δ [σ']))
         in  irrelevanceEqTerm' (PE.sym (singleSubstLift G u)) proj₁[G[u]]' proj₁[G[u]] (app-congTerm proj₁[F] proj₁[G[u]]' proj₁[ΠFG] (proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ']) (proj₁ ([u] ⊢Δ [σ])) proj₁[u'] (proj₂ ([u] ⊢Δ [σ]) [σ'] [σ≡σ'])))

app-congₛ : ∀ {F G t u a b Γ}
            ([Γ] : ⊩ₛ Γ)
            ([F] : Γ ⊩ₛ⟨ ¹ ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ₛ⟨ ¹ ⟩ Π F ▹ G / [Γ])
            ([t≡u] : Γ ⊩ₛ⟨ ¹ ⟩t' t ≡ u ∷ Π F ▹ G / [Γ] / [ΠFG])
            ([a] : Γ ⊩ₛ⟨ ¹ ⟩t a ∷ F / [Γ] / [F])
            ([b] : Γ ⊩ₛ⟨ ¹ ⟩t b ∷ F / [Γ] / [F])
            ([a≡b] : Γ ⊩ₛ⟨ ¹ ⟩t' a ≡ b ∷ F / [Γ] / [F])
          → Γ ⊩ₛ⟨ ¹ ⟩t' t ∘ a ≡ u ∘ b ∷ G [ a ] / [Γ] / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congₛ {F} {G} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]' = irrelevance' (singleSubstLift G a) [G[a]]
  in  irrelevanceEqTerm' (PE.sym (singleSubstLift G a)) [G[a]]' [G[a]]
                         (app-congTerm (proj₁ ([F] ⊢Δ [σ])) [G[a]]' (proj₁ ([ΠFG] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]) (proj₁ ([a] ⊢Δ [σ])) (proj₁ ([b] ⊢Δ [σ])) ([a≡b] ⊢Δ [σ]))
