module Definition.LogicalRelation.Properties where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic

open import Tools.Empty


open import Definition.LogicalRelation.Properties.Reflexivity public
open import Definition.LogicalRelation.Properties.Symmetry public
open import Definition.LogicalRelation.Properties.Transitivity public
open import Definition.LogicalRelation.Properties.Conversion public
open import Definition.LogicalRelation.Properties.Wellformed public
open import Definition.LogicalRelation.Properties.Universe public
open import Definition.LogicalRelation.Properties.Neutral public
open import Definition.LogicalRelation.Properties.Reduction public


maybeEmb : ∀ {l A Γ}
         → Γ ⊩⟨ l ⟩ A
         → Γ ⊩⟨ ¹ ⟩ A
maybeEmb {⁰} [A] = emb {l< = 0<1} [A]
maybeEmb {¹} [A] = [A]

maybeEmb' : ∀ {l A Γ}
          → Γ ⊩⟨ ⁰ ⟩ A
          → Γ ⊩⟨ l ⟩ A
maybeEmb' {⁰} [A] = [A]
maybeEmb' {¹} [A] = emb {l< = 0<1} [A]

sucTerm' : ∀ {l Γ n}
           ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ / ℕ-intr [ℕ]
         → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / ℕ-intr [ℕ]
sucTerm' (noemb (ℕ D)) ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] =
  ℕ[ _ , [ suc ⊢t , suc ⊢t , id (suc ⊢t) ]
   , suc , ℕ[ n , [ ⊢t , ⊢u , d ] , natN , prop ] ]
sucTerm' (emb 0<1 x) [n] = sucTerm' x [n]

sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
        → Γ ⊩⟨ l ⟩ n ∷ ℕ / [ℕ]
        → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / [ℕ]
sucTerm [ℕ] [n] =
  let [n]' = irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n]
  in  irrelevanceTerm (ℕ-intr (ℕ-elim [ℕ]))
                      [ℕ]
                      (sucTerm' (ℕ-elim [ℕ]) [n]')

sucEqTerm' : ∀ {l Γ n n'}
             ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ n ≡ n' ∷ ℕ / ℕ-intr [ℕ]
           → Γ ⊩⟨ l ⟩ suc n ≡ suc n' ∷ ℕ / ℕ-intr [ℕ]
sucEqTerm' (noemb (ℕ D)) ℕ≡[ k , k' , [ ⊢t , ⊢u , d ]
                           , [ ⊢t₁ , ⊢u₁ , d₁ ] , t≡u , prop ] =
  ℕ≡[ _ , _ , idRedTerm:*: (suc ⊢t) , idRedTerm:*: (suc ⊢t₁) , suc-cong t≡u
    , suc ℕ≡[ k , k' , [ ⊢t , ⊢u , d ] , [ ⊢t₁ , ⊢u₁ , d₁ ]
    , t≡u , prop ] ]
sucEqTerm' (emb 0<1 x) [n≡n'] = sucEqTerm' x [n≡n']

sucEqTerm : ∀ {l Γ n n'} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
          → Γ ⊩⟨ l ⟩ n ≡ n' ∷ ℕ / [ℕ]
          → Γ ⊩⟨ l ⟩ suc n ≡ suc n' ∷ ℕ / [ℕ]
sucEqTerm [ℕ] [n≡n'] =
  let [n≡n']' = irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n≡n']
  in  irrelevanceEqTerm (ℕ-intr (ℕ-elim [ℕ])) [ℕ]
                        (sucEqTerm' (ℕ-elim [ℕ]) [n≡n']')
