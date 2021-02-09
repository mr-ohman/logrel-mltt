{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)

open import Tools.Fin
open import Tools.Nat

private
  variable
    ℓ n : Nat
    Γ : Con Term n
    Δ : Con Term ℓ
    ρ : Wk ℓ n
    A A′ B B′ C : Term n
    a a′ b b′ e e′ : Term n
    k l m t u v : Term n

-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term n → (A B : Term n)   → Set

    -- Equality of terms
    _⊢_≅_∷_ : Con Term n → (t u A : Term n) → Set

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term n → (t u A : Term n) → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : Γ ⊢ k ~ l ∷ A
            → Γ ⊢ k ≅ l ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : Γ ⊢ A ≅ B ∷ U
           → Γ ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A
    ~-sym  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A

    -- Transitivity
    ≅-trans  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A
    ~-trans  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A → Γ ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : Γ ⊢ t ≅ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u ∷ B
    ~-conv : Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B

    -- Weakening
    ≅-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ⊢ Γ → Γ ⊢ U ≅ U

    -- Natural number type reflexivity
    ≅-ℕrefl   : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U

    -- Empty type reflexivity
    ≅-Emptyrefl   : ⊢ Γ → Γ ⊢ Empty ≅ Empty
    ≅ₜ-Emptyrefl  : ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ U

    -- Unit type reflexivity
    ≅-Unitrefl   : ⊢ Γ → Γ ⊢ Unit ≅ Unit
    ≅ₜ-Unitrefl  : ⊢ Γ → Γ ⊢ Unit ≅ Unit ∷ U

    -- Unit η-equality
    ≅ₜ-η-unit : Γ ⊢ e ∷ Unit
              → Γ ⊢ e′ ∷ Unit
              → Γ ⊢ e ≅ e′ ∷ Unit

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Π F ▹ G ≅ Π H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → Γ ⊢ Π F ▹ G ≅ Π H ▹ E ∷ U

    -- Σ-congruence

    ≅-Σ-cong  : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Σ F ▹ G ≅ Σ H ▹ E

    ≅ₜ-Σ-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → Γ ⊢ Σ F ▹ G ≅ Σ H ▹ E ∷ U

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ ⊢ F
           → Γ ⊢ f ∷ Π F ▹ G
           → Γ ⊢ g ∷ Π F ▹ G
           → Function f
           → Function g
           → Γ ∙ F ⊢ wk1 f ∘ var x0 ≅ wk1 g ∘ var x0 ∷ G
           → Γ ⊢ f ≅ g ∷ Π F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ∷ Σ F ▹ G
          → Γ ⊢ r ∷ Σ F ▹ G
          → Product p
          → Product r
          → Γ ⊢ fst p ≅ fst r ∷ F
          → Γ ⊢ snd p ≅ snd r ∷ G [ fst p ]
          → Γ ⊢ p ≅ r ∷ Σ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ ⊢ f ~ g ∷ Π F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ]

    -- Product projections congruence
    ~-fst : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ~ r ∷ Σ F ▹ G
          → Γ ⊢ fst p ~ fst r ∷ F

    ~-snd : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ~ r ∷ Σ F ▹ G
          → Γ ⊢ snd p ~ snd r ∷ G [ fst p ]

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ ⊢ F ≅ F′
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ]
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
             → Γ     ⊢ n ~ n′ ∷ ℕ
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ]

    -- Empty recursion congruence
    ~-Emptyrec : ∀ {n n′ F F′}
               → Γ ⊢ F ≅ F′
               → Γ ⊢ n ~ n′ ∷ Empty
               → Γ ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F

  -- Star reflexivity
  ≅ₜ-starrefl : ⊢ Γ → Γ ⊢ star ≅ star ∷ Unit
  ≅ₜ-starrefl [Γ] = ≅ₜ-η-unit (starⱼ [Γ]) (starⱼ [Γ])

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l} → Γ ⊢ k ~ l ∷ U → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)

  ≅-W-cong : ∀ {F G H E} W
          → Γ ⊢ F
          → Γ ⊢ F ≅ H
          → Γ ∙ F ⊢ G ≅ E
          → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong BΠ = ≅-Π-cong
  ≅-W-cong BΣ = ≅-Σ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ ⊢ F
            → Γ ⊢ F ≅ H ∷ U
            → Γ ∙ F ⊢ G ≅ E ∷ U
            → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U
  ≅ₜ-W-cong BΠ = ≅ₜ-Π-cong
  ≅ₜ-W-cong BΣ = ≅ₜ-Σ-cong
