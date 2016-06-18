module Definition.LogicalRelation.PropertiesWIP where

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties

open import Tools.Context

open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as PE


substEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l ⟩ B
substEq (U {l< = l<} ⊢Γ) PE.refl = U {l< = l<} ⊢Γ
substEq (ℕ D) A≡B = ℕ {!D!}
substEq (ne D neK) ne[ M , D' , neM , K≡M ] = ne D' neM
substEq (Π {F} {G} D ⊢F ⊢G [F] [G] G-ext) Π¹[ F' , G' , D' , A≡B , [F≡F'] , [G≡G'] ] =
  Π {F = F'} {G = G'} {!D'!} {!!} {!!}
    (λ ρ ⊢Δ → substEq ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ))
    (λ ρ ⊢Δ [a] → let [a]₁ = convTerm₂ ([F] ρ ⊢Δ) (substEq ([F] ρ ⊢Δ) ([F≡F'] ρ ⊢Δ)) ([F≡F'] ρ ⊢Δ) [a]
                  in  substEq ([G] ρ ⊢Δ [a]₁) ([G≡G'] ρ ⊢Δ [a]₁))
    (λ ρ ⊢Δ [a] [a≡b] → {!!})
substEq {⁰} (emb {l< = ()} x) A≡B
substEq {¹} (emb {l< = 0<1} x) A≡B = emb {l< = 0<1} (substEq x A≡B)

reflNatural : ∀ {Γ n} → (natN : Natural n) → Γ ⊢ n ∷ ℕ → natural-prop Γ n natN → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n n
reflNatural (suc natN) n (proj₁ , proj₂) = suc (reflNatural natN proj₂ proj₁)
reflNatural zero n prop = zero
reflNatural (ne x) n prop = ne x x (refl n)

reflNaturalProp : ∀ {Γ n} (natN : Natural n) (⊢n : Γ ⊢ n ∷ ℕ) (prop : natural-prop Γ n natN) → naturalEq-prop Γ n n (reflNatural natN ⊢n prop)
reflNaturalProp (suc natN) ⊢n (proj₁ , proj₂) = (reflNaturalProp natN proj₂ proj₁) , (refl proj₂)
reflNaturalProp zero ⊢n prop = prop
reflNaturalProp (ne x) ⊢n prop = prop

reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm {⁰} (U {l< = ()} ⊢Γ) (⊢t , ⊩t)
reflEqTerm {¹} (U {l< = 0<1} ⊢Γ) (⊢t , ⊩t) = U[ ⊢t , ⊢t , refl ⊢t , ⊩t , ⊩t , reflEq ⊩t ]
reflEqTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] = ℕ≡[ n , n , d , d , refl ⊢t , reflNatural natN ⊢u prop , reflNaturalProp natN ⊢u prop ]
reflEqTerm (ne D neK) t = refl t
reflEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) (⊢t , [t]) = refl ⊢t , (⊢t , [t]) , (⊢t , [t]) , (λ ρ ⊢Δ [a] → reflEqTerm ([G] ρ ⊢Δ [a]) {!!})
reflEqTerm {⁰} (emb {l< = ()} x) t
reflEqTerm {¹} (emb {l< = 0<1} x) t = reflEqTerm x t


symNatural : ∀ {Γ m n} → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) m n → [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n m
symNatural (suc n₁) = suc (symNatural n₁)
symNatural zero = zero
symNatural (ne x x₁ x₂) = ne x₁ x (sym x₂)

symNaturalProp : ∀ {Γ n n'} ([n≡n'] : [Natural] (λ n₁ n₂ → Γ ⊢ n₁ ≡ n₂ ∷ ℕ) n n')
               → naturalEq-prop Γ n n' [n≡n'] → naturalEq-prop Γ n' n (symNatural [n≡n'])
symNaturalProp (suc [n≡n']) (proj₁ , proj₂) = symNaturalProp [n≡n'] proj₁ , sym proj₂
symNaturalProp zero prop = prop
symNaturalProp (ne x x₁ x₂) prop = prop

symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm {⁰} (U {l< = ()} ⊢Γ) t≡u
symEqTerm {¹} (U {l< = 0<1} ⊢Γ) U[ ⊢t , ⊢u , t≡u , ⊩t , ⊩u , [t≡u] ] = U[ ⊢u , ⊢t , sym t≡u , ⊩u , ⊩t , symEq ⊩t ⊩u [t≡u] ]
symEqTerm (ℕ D) ℕ≡[ k , k' , d , d' , t≡u , [k≡k'] , prop ] = ℕ≡[ k' , k , d' , d , sym t≡u , symNatural [k≡k'] , symNaturalProp [k≡k'] prop ]
symEqTerm (ne D neK) t≡u = sym t≡u
symEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) t≡u = {!!}
symEqTerm {⁰} (emb {l< = ()} x) t≡u
symEqTerm {¹} (emb {l< = 0<1} x) t≡u = symEqTerm x t≡u


-- reflEq : ∀ {Γ A} l ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
-- reflEq ⁰ (ℕ [ ⊢A , ⊢B , D ]) = D
-- reflEq ⁰ (ne [ ⊢A , ⊢B , D ] neK) = ne[ _ , [ ⊢A , ⊢B , D ] , neK , (refl ⊢B) ]
-- reflEq ⁰ (Π {F} {G} [ ⊢A , ⊢B , D ] ⊢F ⊢G [F] [G] G-ext) =
--   Π⁰[ F , G , D , refl ⊢A , (λ ρ ⊢Δ → reflEq ⁰ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ⁰ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ U = PE.refl
-- reflEq ¹ (ℕ ⊢Γ) = id (ℕ ⊢Γ)
-- reflEq ¹ (Π ⊢F ⊢G ⊩F [F] [G] G-ext) = Π¹[ _ , _ , id (Π ⊢F ▹ ⊢G) , refl (Π ⊢F ▹ ⊢G) , (λ ρ ⊢Δ → reflEq ¹ ([F] ρ ⊢Δ)) , (λ ρ ⊢Δ [a] → reflEq ¹ ([G] ρ ⊢Δ [a])) ]
-- reflEq ¹ (emb x) = reflEq ⁰ x
