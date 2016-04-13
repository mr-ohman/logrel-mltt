module Definition.Typed where

open import Tools.Context
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product
open import Definition.Untyped

infixl 30 _∙_

data _∷_∈_ : (x : Nat) (A : Term) (Γ : Con Term) → Set where
  here  : ∀{Γ A}                     →     0 ∷ (wk1 (toCon (size A)) A) ∈ (Γ ∙ A)
  there : ∀{Γ A B n} (h : n ∷ A ∈ Γ) → suc n ∷ (wk1 (toCon (size A)) A) ∈ (Γ ∙ B)

mutual
  data ⊢_ : Con Term → Set where
    ε : ⊢ ε
    _∙_ : ∀ {Γ A} → ⊢ Γ → Γ ⊢ A → ⊢ Γ ∙ A

  data _⊢_ (Γ : Con Term) : Term → Set where
    ℕ-i : ⊢ Γ → Γ ⊢ ℕ
    U-i : ⊢ Γ → Γ ⊢ U
    Π-i : ∀ {F G} → Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ Π F ▹ G
    univ-refl-term : ∀ {A} → Γ ⊢ A ∷ U → Γ ⊢ A

  data _⊢_∷_ (Γ : Con Term) : Term → Term → Set where
--    var-i : ∀ {A} → ⊢ Γ → (x : A ∈ Γ) → Γ ⊢ var (toNat x) ∷ A
    var-i : ∀ {A x} → ⊢ Γ → (x ∷ A ∈ Γ) → Γ ⊢ var x ∷ A
    univ-ℕ-i : ⊢ Γ → Γ ⊢ ℕ ∷ U
    univ-Π-i : ∀ {F G} → Γ ⊢ F ∷ U → Γ ∙ F ⊢ G ∷ U → Γ ⊢ Π F ▹ G ∷ U
    λ-i : ∀ {F G t} → Γ ∙ F ⊢ t ∷ G → Γ ⊢ lam t ∷ (Π F ▹ G)
    fun-e : ∀ {g a F G} → Γ ⊢ g ∷ Π F ▹ G → Γ ⊢ a ∷ F → Γ ⊢ g ∘ a ∷ G [ a ]
    zero : ⊢ Γ → Γ ⊢ zero ∷ ℕ
    suc : ∀ {n} → Γ ⊢ n ∷ ℕ → Γ ⊢ suc n ∷ ℕ
    natrec-i : ∀ {G s z} → Γ ∙ ℕ ⊢ G → Γ ⊢ z ∷ G [ zero ]
             → Γ ⊢ s ∷ Π ℕ ▹ Π G [ var zero ] ▹ G [ suc (var (suc zero)) ]
             → Γ ⊢ natrec G z s ∷ Π ℕ ▹ G
    eq-type-term : ∀ {t A B} → Γ ⊢ t ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ∷ B

  data _⊢_≡_ (Γ : Con Term) : Term → Term → Set where
    univ-refl : ∀ {A B} → Γ ⊢ A ≡ B ∷ U → Γ ⊢ A ≡ B
    refl : ∀ {A} → Γ ⊢ A → Γ ⊢ A ≡ A
    sym  : ∀ {A B} → Γ ⊢ A ≡ B → Γ ⊢ B ≡ A
    trans : ∀ {A B C} → Γ ⊢ A ≡ B → Γ ⊢ B ≡ C → Γ ⊢ A ≡ C
    Π-eq : ∀ {E F G H} → Γ ⊢ F ≡ H → Γ ∙ F ⊢ G ≡ E
         → Γ ⊢ Π F ▹ G ≡ Π H ▹ E

  data _⊢_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
    refl : ∀ {t A} → Γ ⊢ t ∷ A → Γ ⊢ t ≡ t ∷ A
    sym : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ t ∷ A
    trans : ∀ {t u r A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ r ∷ A → Γ ⊢ t ≡ r ∷ A
    eq-type-term : ∀ {A B t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ B
    Π-eq-univ : ∀ {E F G H} → Γ ⊢ F ≡ H ∷ U → Γ ∙ F ⊢ G ≡ E ∷ U
              → Γ ⊢ Π F ▹ G ≡ Π H ▹ E ∷ U
    fun-eq : ∀ {a b f g F G} → Γ ⊢ f ≡ g ∷ Π F ▹ G → Γ ⊢ a ≡ b ∷ F
           → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    -- fun-eq : ∀ {a f g F G} → Γ ⊢ f ≡ g ∷ Π F ▹ G → Γ ⊢ a ∷ F
    --        → Γ ⊢ f ∘ a ≡ g ∘ a ∷ G [ a ]
    -- fun : ∀ {a b f F G} → Γ ⊢ f ∷ Π F ▹ G → Γ ⊢ a ≡ b ∷ F
    --     → Γ ⊢ f ∘ a ≡ f ∘ b ∷ G [ a ]
    β-red : ∀ {a b F G} → Γ ∙ F ⊢ b ∷ G → Γ ⊢ a ∷ F
          → Γ ⊢ (lam b) ∘ a ≡ b [ a ] ∷ G [ a ]
    fun-ext : ∀ {f g F G A} → Γ ⊢ f ∷ Π F ▹ G → Γ ⊢ g ∷ Π F ▹ G
            → Γ ∙ A ⊢ f ∘ var zero ≡ g ∘ var zero ∷ G [ var zero ]
            → Γ ⊢ f ≡ g ∷ Π F ▹ G
    natrec-eq : ∀ {z z' s s' F F'} → Γ ∙ ℕ ⊢ F ≡ F' → Γ ⊢ z ≡ z' ∷ F [ zero ]
              → Γ ⊢ s ≡ s' ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
              → Γ ⊢ natrec F z s ≡ natrec F' z' s' ∷ Π ℕ ▹ F
    natrec-zero : ∀ {z s F} → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
                → Γ ⊢ s ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
                → Γ ⊢ natrec F z s ∘ zero ≡ z ∷ F [ zero ]
    natrec-suc : ∀ {n z s F} → Γ ⊢ n ∷ ℕ → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
               → Γ ⊢ s ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
               → Γ ⊢ natrec F z s ∘ suc n
                 ≡ (s ∘ n) ∘ (natrec F z s ∘ n) ∷ F [ suc n ]
    -- congruence rule for suc

data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  natrec-subst : ∀ {C c g m n} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
               → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
               → Γ ⊢ m ⇒ n ∷ ℕ
               → Γ ⊢ natrec C c g ∘ m ⇒ natrec C c g ∘ n ∷ C [ n ]
  natrec-zero : ∀ {C c g} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
              → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
              → Γ ⊢ natrec C c g ∘ zero ⇒ c ∷ C [ zero ]
  natrec-suc : ∀ {C c g n} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
             → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
             → Γ ⊢ natrec C c g ∘ suc n
               ⇒ (g ∘ n) ∘ (natrec C c g ∘ n) ∷ C [ suc n ]
  app-subst : ∀ {A B t t' a} → Γ ⊢ t ⇒ t' ∷ Π A ▹ B → Γ ⊢ a ∷ A
            → Γ ⊢ t ∘ a ⇒ t' ∘ a ∷ B [ a ]
  β-red : ∀ {A B a t} → Γ ∙ A ⊢ t ∷ B → Γ ⊢ a ∷ A
        → Γ ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  eq-type-term : ∀ {A B t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒ u ∷ B

data _⊢_⇒_ (Γ : Con Term) : Term → Term → Set where
  univ-refl : ∀ {A B} → Γ ⊢ A ⇒ B ∷ U → Γ ⊢ A ⇒ B

data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id : ∀ {A t} → Γ ⊢ t ⇒* t ∷ A
  arrow : ∀ {A t t' u} → Γ ⊢ t ⇒ t' ∷ A → Γ ⊢ t' ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A

data _⊢_⇒*_ (Γ : Con Term) : Term → Term → Set where
  id : ∀ {A} → Γ ⊢ A ⇒* A
  arrow : ∀ {A A' B} → Γ ⊢ A ⇒ A' → Γ ⊢ A' ⇒* B → Γ ⊢ A ⇒* B

_⊢_⇒⁺_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ⇒⁺ u ∷ A = ∀ {t'} → Γ ⊢ t ⇒ t' ∷ A × Γ ⊢ t' ⇒* u ∷ A

_⊢_⇒⁺_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A ⇒⁺ B = ∀ {A'} → Γ ⊢ A ⇒ A' × Γ ⊢ A' ⇒* B
