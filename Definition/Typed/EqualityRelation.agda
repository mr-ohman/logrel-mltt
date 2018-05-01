{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)


-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term → (A B : Term)   → Set

    -- Equality of terms
    _⊢_≅_∷_ : Con Term → (t u A : Term) → Set

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term → (t u A : Term) → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : ∀ {k l A Γ}
            → Γ ⊢ k ~ l ∷ A
            → Γ ⊢ k ≅ l ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : ∀ {A B Γ}
          → Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : ∀ {t u A Γ}
          → Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : ∀ {A B Γ}
           → Γ ⊢ A ≅ B ∷ U
           → Γ ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : ∀ {A B Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : ∀ {t u A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A
    ~-sym  : ∀ {k l A Γ} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A

    -- Transitivity
    ≅-trans  : ∀ {A B C Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : ∀ {t u v A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A
    ~-trans  : ∀ {k l m A Γ} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A → Γ ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : ∀ {t u A B Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u ∷ B
    ~-conv : ∀ {k l A B Γ} → Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B

    -- Weakening
    ≅-wk  : ∀ {A B ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ∀ {t u A ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ∀ {k l A ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A

    -- Weak head expansion
    ≅-red : ∀ {A A′ B B′ Γ}
          → Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : ∀ {a a′ b b′ A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ U ≅ U

    -- Natural number type reflexivity
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U

    -- Π-congurence

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

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    -- Successor congurence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- η-equality
    ≅-η-eq : ∀ {f g F G Γ}
              → Γ ⊢ F
              → Γ ⊢ f ∷ Π F ▹ G
              → Γ ⊢ g ∷ Π F ▹ G
              → Function f
              → Function g
              → Γ ∙ F ⊢ wk1 f ∘ var 0 ≅ wk1 g ∘ var 0 ∷ G
              → Γ ⊢ f ≅ g ∷ Π F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A Γ} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A

    -- Application congurence
    ~-app : ∀ {a b f g F G Γ}
          → Γ ⊢ f ~ g ∷ Π F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ]

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ Γ}
             → Γ ∙ ℕ ⊢ F ≅ F′
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ]
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var 0) ]↑)
             → Γ     ⊢ n ~ n′ ∷ ℕ
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ]


  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l Γ} → Γ ⊢ k ~ l ∷ U → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)
