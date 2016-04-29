module Definition.Typed where

open import Tools.Context
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product
open import Definition.Untyped

infixl 30 _∙_
infix 30 Π_▹_

data _∷_∈_ : (x : Nat) (A : Term) (Γ : Con Term) → Set where
  here  : ∀{Γ A}                     →     0 ∷ wk1 A ∈ (Γ ∙ A)
  there : ∀{Γ A B n} (h : n ∷ A ∈ Γ) → suc n ∷ wk1 A ∈ (Γ ∙ B)

mutual
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A} → ⊢ Γ → Γ ⊢ A → ⊢ Γ ∙ A

  data _⊢_ (Γ : Con Term) : Term → Set where
    ℕ    : ⊢ Γ → Γ ⊢ ℕ
    U    : ⊢ Γ → Γ ⊢ U
    Π_▹_ : ∀ {F G} → Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ Π F ▹ G
    univ : ∀ {A} → Γ ⊢ A ∷ U → Γ ⊢ A

  data _⊢_∷_ (Γ : Con Term) : Term → Term → Set where
    ℕ      : ⊢ Γ → Γ ⊢ ℕ ∷ U
    Π_▹_   : ∀ {F G} → Γ ⊢ F ∷ U → Γ ∙ F ⊢ G ∷ U → Γ ⊢ Π F ▹ G ∷ U
    var    : ∀ {A x} → ⊢ Γ → x ∷ A ∈ Γ → Γ ⊢ var x ∷ A
    lam    : ∀ {F G t} → Γ ∙ F ⊢ t ∷ G → Γ ⊢ lam t ∷ Π F ▹ G
    _∘_    : ∀ {g a F G} → Γ ⊢ g ∷ Π F ▹ G → Γ ⊢ a ∷ F → Γ ⊢ g ∘ a ∷ G [ a ]
    zero   : ⊢ Γ → Γ ⊢ zero ∷ ℕ
    suc    : ∀ {n} → Γ ⊢ n ∷ ℕ → Γ ⊢ suc n ∷ ℕ
    natrec : ∀ {G s z} → Γ ∙ ℕ ⊢ G → Γ ⊢ z ∷ G [ zero ]
           → Γ ⊢ s ∷ Π ℕ ▹ Π G [ var zero ] ▹ G [ suc (var (suc zero)) ]
           → Γ ⊢ natrec G z s ∷ Π ℕ ▹ G
    conv   : ∀ {t A B} → Γ ⊢ t ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ∷ B

  data _⊢_≡_ (Γ : Con Term) : Term → Term → Set where
    univ   : ∀ {A B} → Γ ⊢ A ≡ B ∷ U → Γ ⊢ A ≡ B
    refl   : ∀ {A} → Γ ⊢ A → Γ ⊢ A ≡ A
    sym    : ∀ {A B} → Γ ⊢ A ≡ B → Γ ⊢ B ≡ A
    trans  : ∀ {A B C} → Γ ⊢ A ≡ B → Γ ⊢ B ≡ C → Γ ⊢ A ≡ C
    Π-cong : ∀ {E F G H} → Γ ⊢ F ≡ H → Γ ∙ F ⊢ G ≡ E
           → Γ ⊢ Π F ▹ G ≡ Π H ▹ E

  data _⊢_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
    refl     : ∀ {t A} → Γ ⊢ t ∷ A → Γ ⊢ t ≡ t ∷ A
    sym      : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ t ∷ A
    trans    : ∀ {t u r A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ r ∷ A → Γ ⊢ t ≡ r ∷ A
    conv     : ∀ {A B t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ B
    Π-cong   : ∀ {E F G H} → Γ ⊢ F ≡ H ∷ U → Γ ∙ F ⊢ G ≡ E ∷ U
             → Γ ⊢ Π F ▹ G ≡ Π H ▹ E ∷ U
    app-cong : ∀ {a b f g F G} → Γ ⊢ f ≡ g ∷ Π F ▹ G → Γ ⊢ a ≡ b ∷ F
             → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    β-red    : ∀ {a b F G} → Γ ∙ F ⊢ b ∷ G → Γ ⊢ a ∷ F
             → Γ ⊢ (lam b) ∘ a ≡ b [ a ] ∷ G [ a ]
    fun-ext  : ∀ {f g F G} → Γ ⊢ f ∷ Π F ▹ G → Γ ⊢ g ∷ Π F ▹ G
             → Γ ∙ F ⊢ f ∘ var zero ≡ g ∘ var zero ∷ G [ var zero ]
             → Γ ⊢ f ≡ g ∷ Π F ▹ G
    suc-cong : ∀ {m n} → Γ ⊢ m ≡ n ∷ ℕ → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong : ∀ {z z' s s' F F'} → Γ ∙ ℕ ⊢ F ≡ F' → Γ ⊢ z ≡ z' ∷ F [ zero ]
                → Γ ⊢ s ≡ s' ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
                → Γ ⊢ natrec F z s ≡ natrec F' z' s' ∷ Π ℕ ▹ F
    natrec-zero : ∀ {z s F} → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
                → Γ ⊢ s ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
                → Γ ⊢ natrec F z s ∘ zero ≡ z ∷ F [ zero ]
    natrec-suc  : ∀ {n z s F} → Γ ⊢ n ∷ ℕ → Γ ∙ ℕ ⊢ F → Γ ⊢ z ∷ F [ zero ]
                → Γ ⊢ s ∷ Π ℕ ▹ Π F [ var zero ] ▹ F [ suc (var (suc zero)) ]
                → Γ ⊢ natrec F z s ∘ suc n ≡ (s ∘ n) ∘ (natrec F z s ∘ n)
                    ∷ F [ suc n ]

data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  conv      : ∀ {A B t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒ u ∷ B
  app-subst : ∀ {A B t t' a} → Γ ⊢ t ⇒ t' ∷ Π A ▹ B → Γ ⊢ a ∷ A
            → Γ ⊢ t ∘ a ⇒ t' ∘ a ∷ B [ a ]
  β-red     : ∀ {A B a t} → Γ ∙ A ⊢ t ∷ B → Γ ⊢ a ∷ A
            → Γ ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  natrec-subst : ∀ {C c g m n} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
               → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
               → Γ ⊢ m ⇒ n ∷ ℕ
               → Γ ⊢ natrec C c g ∘ m ⇒ natrec C c g ∘ n ∷ C [ n ]
  natrec-zero  : ∀ {C c g} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
               → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
               → Γ ⊢ natrec C c g ∘ zero ⇒ c ∷ C [ zero ]
  natrec-suc   : ∀ {C c g n} → Γ ⊢ n ∷ ℕ → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
               → Γ ⊢ g ∷ Π ℕ ▹ Π C [ var zero ] ▹ C [ suc (var (suc zero)) ]
               → Γ ⊢ natrec C c g ∘ suc n ⇒ (g ∘ n) ∘ (natrec C c g ∘ n)
                   ∷ C [ suc n ]

data _⊢_⇒_ (Γ : Con Term) : Term → Term → Set where
  univ : ∀ {A B} → Γ ⊢ A ⇒ B ∷ U → Γ ⊢ A ⇒ B

data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id  : ∀ {A t} → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t' u} → Γ ⊢ t ⇒ t' ∷ A → Γ ⊢ t' ⇒* u ∷ A → Γ ⊢ t ⇒* u ∷ A

data _⊢_⇒*_ (Γ : Con Term) : Term → Term → Set where
  id  : ∀ {A} → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A' B} → Γ ⊢ A ⇒ A' → Γ ⊢ A' ⇒* B → Γ ⊢ A ⇒* B

_⊢_⇒⁺_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ⇒⁺ u ∷ A = ∀ {t'} → Γ ⊢ t ⇒ t' ∷ A × Γ ⊢ t' ⇒* u ∷ A

_⊢_⇒⁺_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A ⇒⁺ B = ∀ {A'} → Γ ⊢ A ⇒ A' × Γ ⊢ A' ⇒* B
