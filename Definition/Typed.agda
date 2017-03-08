{-# OPTIONS --without-K #-}

module Definition.Typed where

open import Tools.Nat
open import Tools.Product
open import Definition.Untyped

infixl 30 _∙_
infix 30 Π_▹_


-- Context member existance at location
data _∷_∈_ : (x : Nat) (A : Term) (Γ : Con Term) → Set where
  here  : ∀ {Γ A}                     →     0 ∷ wk1 A ∈ (Γ ∙ A)
  there : ∀ {Γ A B n} (h : n ∷ A ∈ Γ) → suc n ∷ wk1 A ∈ (Γ ∙ B)

mutual
  -- Well-formed context
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A}
        → ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term) : Term → Set where
    ℕ    : ⊢ Γ → Γ ⊢ ℕ
    U    : ⊢ Γ → Γ ⊢ U
    Π_▹_ : ∀ {F G}
         → Γ     ⊢ F
         → Γ ∙ F ⊢ G
         → Γ     ⊢ Π F ▹ G
    univ : ∀ {A}
         → Γ ⊢ A ∷ U
         → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term) : Term → Term → Set where
    ℕ      : ⊢ Γ → Γ ⊢ ℕ ∷ U
    Π_▹_   : ∀ {F G}
           → Γ     ⊢ F ∷ U
           → Γ ∙ F ⊢ G ∷ U
           → Γ     ⊢ Π F ▹ G ∷ U
    var    : ∀ {A x}
           → ⊢ Γ
           → x ∷ A ∈ Γ
           → Γ ⊢ var x ∷ A
    lam    : ∀ {F G t}
           → Γ     ⊢ F
           → Γ ∙ F ⊢ t ∷ G
           → Γ     ⊢ lam t ∷ Π F ▹ G
    _∘_    : ∀ {g a F G}
           → Γ ⊢     g ∷ Π F ▹ G
           → Γ ⊢     a ∷ F
           → Γ ⊢ g ∘ a ∷ G [ a ]
    zero   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ
    suc    : ∀ {n}
           → Γ ⊢     n ∷ ℕ
           → Γ ⊢ suc n ∷ ℕ
    natrec : ∀ {G s z n}
           → Γ ∙ ℕ ⊢ G
           → Γ     ⊢ z ∷ G [ zero ]
           → Γ     ⊢ s ∷ Π ℕ ▹ (G ▹▹ G [ suc (var zero) ]↑)
           → Γ     ⊢ n ∷ ℕ
           → Γ     ⊢ natrec G z s n ∷ G [ n ]
    conv   : ∀ {t A B}
           → Γ ⊢ t ∷ A
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ∷ B

  -- Type equality
  data _⊢_≡_ (Γ : Con Term) : Term → Term → Set where
    univ   : ∀ {A B}
           → Γ ⊢ A ≡ B ∷ U
           → Γ ⊢ A ≡ B
    refl   : ∀ {A}
           → Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : ∀ {A B}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : ∀ {A B C}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    Π-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
    refl        : ∀ {t A}
                → Γ ⊢ t ∷ A
                → Γ ⊢ t ≡ t ∷ A
    sym         : ∀ {t u A}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ u ≡ t ∷ A
    trans       : ∀ {t u r A}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ u ≡ r ∷ A
                → Γ ⊢ t ≡ r ∷ A
    conv        : ∀ {A B t u}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ A ≡ B
                → Γ ⊢ t ≡ u ∷ B
    Π-cong      : ∀ {E F G H}
                → Γ     ⊢ F
                → Γ     ⊢ F ≡ H       ∷ U
                → Γ ∙ F ⊢ G ≡ E       ∷ U
                → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E ∷ U
    app-cong    : ∀ {a b f g F G}
                → Γ ⊢ f ≡ g ∷ Π F ▹ G
                → Γ ⊢ a ≡ b ∷ F
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    β-red       : ∀ {a t F G}
                → Γ     ⊢ F
                → Γ ∙ F ⊢ t ∷ G
                → Γ     ⊢ a ∷ F
                → Γ     ⊢ (lam t) ∘ a ≡ t [ a ] ∷ G [ a ]
    fun-ext     : ∀ {f g F G}
                → Γ     ⊢ F
                → Γ     ⊢ f ∷ Π F ▹ G
                → Γ     ⊢ g ∷ Π F ▹ G
                → Γ ∙ F ⊢ wk1 f ∘ var zero ≡ wk1 g ∘ var zero ∷ G
                → Γ     ⊢ f ≡ g ∷ Π F ▹ G
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ
                → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong : ∀ {z z' s s' n n' F F'}
                → Γ ∙ ℕ ⊢ F ≡ F'
                → Γ     ⊢ z ≡ z' ∷ F [ zero ]
                → Γ     ⊢ s ≡ s' ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                → Γ     ⊢ n ≡ n' ∷ ℕ
                → Γ     ⊢ natrec F z s n ≡ natrec F' z' s' n' ∷ F [ n ]
    natrec-zero : ∀ {z s F}
                → Γ ∙ ℕ ⊢ F
                → Γ     ⊢ z ∷ F [ zero ]
                → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ]
    natrec-suc  : ∀ {n z s F}
                → Γ     ⊢ n ∷ ℕ
                → Γ ∙ ℕ ⊢ F
                → Γ     ⊢ z ∷ F [ zero ]
                → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ]

-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  conv         : ∀ {A B t u}
               → Γ ⊢ t ⇒ u ∷ A
               → Γ ⊢ A ≡ B
               → Γ ⊢ t ⇒ u ∷ B
  app-subst    : ∀ {A B t u a}
               → Γ ⊢ t ⇒ u ∷ Π A ▹ B
               → Γ ⊢ a ∷ A
               → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  β-red        : ∀ {A B a t}
               → Γ     ⊢ A
               → Γ ∙ A ⊢ t ∷ B
               → Γ     ⊢ a ∷ A
               → Γ     ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  natrec-subst : ∀ {z s n n' F}
               → Γ ∙ ℕ ⊢ F
               → Γ     ⊢ z ∷ F [ zero ]
               → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
               → Γ     ⊢ n ⇒ n' ∷ ℕ
               → Γ     ⊢ natrec F z s n ⇒ natrec F z s n' ∷ F [ n ]
  natrec-zero  : ∀ {z s F}
               → Γ ∙ ℕ ⊢ F
               → Γ     ⊢ z ∷ F [ zero ]
               → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
               → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc   : ∀ {n z s F}
               → Γ     ⊢ n ∷ ℕ
               → Γ ∙ ℕ ⊢ F
               → Γ     ⊢ z ∷ F [ zero ]
               → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
               → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                       ∷ F [ suc n ]

-- Type reduction
data _⊢_⇒_ (Γ : Con Term) : Term → Term → Set where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t' u}
      → Γ ⊢ t  ⇒  t' ∷ A
      → Γ ⊢ t' ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term) : Term → Term → Set where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A' B}
      → Γ ⊢ A  ⇒  A'
      → Γ ⊢ A' ⇒* B
      → Γ ⊢ A  ⇒* B

-- Term reduction closure with at least one reduction
_⊢_⇒⁺_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ⇒⁺ u ∷ A = ∀ {t'} → Γ ⊢ t ⇒ t' ∷ A × Γ ⊢ t' ⇒* u ∷ A

-- Type reduction closure with at least one reduction
_⊢_⇒⁺_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A ⇒⁺ B = ∀ {A'} → Γ ⊢ A ⇒ A' × Γ ⊢ A' ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type eqaulity with well-formed types
_⊢_:≡:_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t :≡: u ∷ A = Γ ⊢ t ∷ A × Γ ⊢ u ∷ A × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term) (A B : Term) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ) public
