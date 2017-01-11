module Definition.EqualityRelation where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening

open import Tools.Nat

record EqRelSet : Set₁ where
  constructor eqRel
  field
    _⊢_≅_   : Con Term → (A B : Term)   → Set
    _⊢_≅_∷_ : Con Term → (t u A : Term) → Set

    ≅-Urefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ U ≅ U
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U

    -- Only used in neu in Neutral.agda
    ≅-nerefl  : ∀ {K Γ} → Γ ⊢ K → Neutral K → Γ ⊢ K ≅ K

    ≅ₜ-nerefl : ∀ {k A Γ} → Γ ⊢ k ∷ A → Neutral k → Γ ⊢ k ≅ k ∷ A
    ≅ₜ-varrefl : ∀ {x A Γ} → Γ ⊢ var x ∷ A → Γ ⊢ var x ≅ var x ∷ A
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    ≅-sym  : ∀ {A B Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : ∀ {t u A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A

    ≅-trans  : ∀ {A B C Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : ∀ {t u v A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A

    ≅-red : ∀ {A A' B B' Γ}
          → Γ ⊢ A ⇒* A'
          → Γ ⊢ B ⇒* B'
          → Whnf A'
          → Whnf B'
          → Γ ⊢ A' ≅ B'
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : ∀ {a a' b b' A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a' ∷ B
           → Γ ⊢ b ⇒* b' ∷ B
           → Whnf B
           → Whnf a'
           → Whnf b'
           → Γ ⊢ a' ≅ b' ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    ≅-wk  : ∀ {A B ρ Γ Δ}
          → ρ ∷ Γ ⊆ Δ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ U.wk ρ A ≅ U.wk ρ B
    ≅ₜ-wk : ∀ {t u A ρ Γ Δ}
          → ρ ∷ Γ ⊆ Δ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ U.wk ρ t ≅ U.wk ρ u ∷ U.wk ρ A

    ≅-eq  : ∀ {A B Γ}
          → Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : ∀ {t u A Γ}
          → Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    ≅-conv : ∀ {t u A B Γ}
           → Γ ⊢ t ≅ u ∷ A
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ≅ u ∷ B

    ≅-univ : ∀ {A B Γ}
           → Γ ⊢ A ≅ B ∷ U
           → Γ ⊢ A ≅ B

    -- Only used for neuTerm in Neutral.agda
    ≅-app-cong : ∀ {a b f g F G Γ}
               → Γ ⊢ f ≅ g ∷ Π F ▹ G
               → Γ ⊢ a ≅ b ∷ F
               → Γ ⊢ f ∘ a ≅ g ∘ b ∷ G [ a ]

    -- Used for neuEqTerm in Neutral.agda and fun-extEqTerm in Lambda.agda
    ≅-app-subst : ∀ {a f g F G Γ}
                → Γ ⊢ f ≅ g ∷ Π F ▹ G
                → Γ ⊢ a ∷ F
                → Γ ⊢ f ∘ a ≅ g ∘ a ∷ G [ a ]

    ≅-suc-cong : ∀ {m n Γ}
               → Γ ⊢ m ≅ n ∷ ℕ
               → Γ ⊢ suc m ≅ suc n ∷ ℕ

    ≅-Π-cong  : ∀ {F G H E Γ}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Π F ▹ G ≅ Π H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E Γ}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → Γ ⊢ Π F ▹ G ≅ Π H ▹ E ∷ U

    -- Only used for the neutral case of natrec-congTerm in Natrec.agda
    ≅-natrec-cong : ∀ {z z' s s' n n' F F' Γ}
                  → Γ ∙ ℕ ⊢ F ≅ F'
                  → Γ     ⊢ z ≅ z' ∷ F [ zero ]
                  → Γ     ⊢ s ≅ s' ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                  → Γ     ⊢ n ≅ n' ∷ ℕ
                  → Γ     ⊢ natrec F z s n ≅ natrec F' z' s' n' ∷ F [ n ]

    ≅-fun-ext : ∀ {f g F G Γ}
              → Γ ⊢ F
              → Γ ⊢ f ∷ Π F ▹ G
              → Γ ⊢ g ∷ Π F ▹ G
              → Whnf f
              → Whnf g
              → Γ ∙ F ⊢ wk1 f ∘ var zero ≅ wk1 g ∘ var zero ∷ G
              → Γ ⊢ f ≅ g ∷ Π F ▹ G
