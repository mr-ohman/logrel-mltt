module Definition.LogicalRelation.Properties where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Data.Empty


open import Definition.LogicalRelation.Properties.Reflexivity public
open import Definition.LogicalRelation.Properties.Symmetry public
open import Definition.LogicalRelation.Properties.Transitivity public
open import Definition.LogicalRelation.Properties.Conversion public
open import Definition.LogicalRelation.Properties.Soundness public
open import Definition.LogicalRelation.Properties.Univalence public
open import Definition.LogicalRelation.Properties.Neutral public
open import Definition.LogicalRelation.Properties.Reduction public


maybeEmb : ∀ {l A Γ}
         → Γ ⊩⟨ l ⟩ A
         → Γ ⊩⟨ ¹ ⟩ A
maybeEmb {⁰} [A] = emb {l< = 0<1} [A]
maybeEmb {¹} [A] = [A]

sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ) → Γ ⊩⟨ l ⟩ n ∷ ℕ / [ℕ] → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / [ℕ]
sucTerm (ℕ D) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] = ℕ[ _ , [ suc ⊢t , suc ⊢t , id (suc ⊢t) ] , suc , ⊢t ]
sucTerm (ne D neK) [n] = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
sucTerm (Π D ⊢F ⊢G [F] [G] G-ext) [n] = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
sucTerm (emb {l< = 0<1} x) [n] = sucTerm x [n]

sucEqTerm : ∀ {l Γ n n'} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ) → Γ ⊩⟨ l ⟩ n ≡ n' ∷ ℕ / [ℕ] → Γ ⊩⟨ l ⟩ suc n ≡ suc n' ∷ ℕ / [ℕ]
sucEqTerm (ℕ D) ℕ≡[ k , k' , [ ⊢t , ⊢u , d ] , [ ⊢t₁ , ⊢u₁ , d₁ ] , t≡u , [k≡k'] ] = ℕ≡[ _ , _ , idRedTerm:*: (suc ⊢t) , idRedTerm:*: (suc ⊢t₁) , suc-cong t≡u , suc t≡u ]
sucEqTerm (ne D neK) [n≡n'] = ⊥-elim (ℕ≢ne neK (whnfRed*' (red D) ℕ))
sucEqTerm (Π D ⊢F ⊢G [F] [G] G-ext) [n≡n'] = ⊥-elim (ℕ≢Π (whnfRed*' (red D) ℕ))
sucEqTerm (emb {l< = 0<1} x) [n≡n'] = sucEqTerm x [n≡n']
