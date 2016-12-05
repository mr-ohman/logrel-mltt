module Definition.Conversion where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat


infix 10 _⊢_~_↑_
infix 10 _⊢_[conv]_
infix 10 _⊢_[conv]_∷_

mutual
  data _⊢_~_↑_ (Γ : Con Term) : (k l A : Term) → Set where
    var    : ∀ {x A}
           → Γ ⊢ var x ∷ A
           → Γ ⊢ var x ~ var x ↑ A
    app    : ∀ {k l t v F G}
           → Γ ⊢ k ~ l ↑ Π F ▹ G
           → Γ ⊢ k ∷ Π F ▹ G
           → Γ ⊢ t [conv] v ∷ F
           → Γ ⊢ k ∘ t ~ l ∘ v ↑ G [ t ]
    suc    : ∀ {k l}
           → Γ ⊢ k ~ l ↑ ℕ
           → Γ ⊢ k ∷ ℕ
           → Γ ⊢ suc k ~ suc l ↑ ℕ
    natrec : ∀ {k l h g a₀ b₀ F G}
           → Γ ⊢ k ~ l ↑ ℕ
           → Γ ⊢ k ∷ ℕ
           → Γ ∙ ℕ ⊢ F [conv] G
           → Γ ⊢ h [conv] g ∷ Π ℕ ▹ (F ▹▹ F [ suc (var zero) ]↑)
           → Γ ⊢ a₀ [conv] b₀ ∷ F [ zero ]
           → Γ ⊢ natrec F a₀ h k ~ natrec G b₀ g l ↑ F [ k ]

  data _⊢_[conv]_ (Γ : Con Term) : (A B : Term) → Set where
    reduction : ∀ {A A' B B'}
              → Γ ⊢ A ⇒* A'
              → Γ ⊢ B ⇒* B'
              → Γ ⊢ A' [conv] B'
              → Γ ⊢ A [conv] B
    U-refl    : ⊢ Γ → Γ ⊢ U [conv] U
    ℕ-refl    : ⊢ Γ → Γ ⊢ ℕ [conv] ℕ
    ne        : ∀ {K L}
              → Γ ⊢ K ~ L ↑ U
              → Γ ⊢ K
              → Neutral K
              → Neutral L
              → Γ ⊢ K [conv] L
    Π-cong    : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F [conv] H
              → Γ ∙ F ⊢ G [conv] E
              → Γ ⊢ Π F ▹ G [conv] Π H ▹ E

  data _⊢_[conv]_∷_ (Γ : Con Term) : (t u A : Term) → Set where
    reduction : ∀ {a a' b b' A B}
              → Γ ⊢ A ⇒* B
              → Γ ⊢ a ⇒* a' ∷ B
              → Γ ⊢ b ⇒* b' ∷ B
              → Γ ⊢ a' [conv] b' ∷ B
              → Γ ⊢ a [conv] b ∷ A
    ℕ-ins     : ∀ {k l A}
              → Γ ⊢ k ~ l ↑ A
              → Γ ⊢ A ⇒* ℕ
              → Γ ⊢ k ∷ A
              → Γ ⊢ k [conv] l ∷ A
    ne-ins    : ∀ {k l A M}
              → Γ ⊢ k ~ l ↑ A
              → Γ ⊢ A ⇒* M
              → Γ ⊢ k ∷ A
              → Neutral M
              → Γ ⊢ k [conv] l ∷ A
    univ      : ∀ {A B}
              → Γ ⊢ A ∷ U
              → Γ ⊢ B ∷ U
              → Γ ⊢ A [conv] B
              → Γ ⊢ A [conv] B ∷ U
    zero-refl : ⊢ Γ → Γ ⊢ zero [conv] zero ∷ ℕ
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv] n ∷ ℕ
              → Γ ⊢ suc m [conv] suc n ∷ ℕ
    fun-ext   : ∀ {f g F G}
              → Γ ⊢ F
              → Γ ⊢ f ∷ Π F ▹ G
              → Γ ⊢ g ∷ Π F ▹ G
              → Γ ∙ F ⊢ wk1 f ∘ var zero [conv] wk1 g ∘ var zero ∷ G
              → Γ ⊢ f [conv] g ∷ Π F ▹ G
