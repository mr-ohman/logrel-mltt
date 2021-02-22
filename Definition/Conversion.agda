-- Algorithmic equality.

{-# OPTIONS --without-K --safe #-}

module Definition.Conversion where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_
infix 10 _⊢_~_↓_
infix 10 _⊢_[conv↑]_
infix 10 _⊢_[conv↓]_
infix 10 _⊢_[conv↑]_∷_
infix 10 _⊢_[conv↓]_∷_

private
  variable
    n : Nat
    Γ : Con Term n

mutual
  -- Neutral equality.
  data _⊢_~_↑_ (Γ : Con Term n) : (k l A : Term n) → Set where
    var-refl      : ∀ {x y A}
                  → Γ ⊢ var x ∷ A
                  → x PE.≡ y
                  → Γ ⊢ var x ~ var y ↑ A
    app-cong      : ∀ {k l t v F G}
                  → Γ ⊢ k ~ l ↓ Π F ▹ G
                  → Γ ⊢ t [conv↑] v ∷ F
                  → Γ ⊢ k ∘ t ~ l ∘ v ↑ G [ t ]
    fst-cong      : ∀ {p r F G}
                  → Γ ⊢ p ~ r ↓ Σ F ▹ G
                  → Γ ⊢ fst p ~ fst r ↑ F
    snd-cong      : ∀ {p r F G}
                  → Γ ⊢ p ~ r ↓ Σ F ▹ G
                  → Γ ⊢ snd p ~ snd r ↑ G [ fst p ]
    natrec-cong   : ∀ {k l h g a₀ b₀ F G}
                  → Γ ∙ ℕ ⊢ F [conv↑] G
                  → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ]
                  → Γ ⊢ h [conv↑] g ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ ⊢ k ~ l ↓ ℕ
                  → Γ ⊢ natrec F a₀ h k ~ natrec G b₀ g l ↑ F [ k ]
    Emptyrec-cong : ∀ {k l F G}
                  → Γ ⊢ F [conv↑] G
                  → Γ ⊢ k ~ l ↓ Empty
                  → Γ ⊢ Emptyrec F k ~ Emptyrec G l ↑ F

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓_ (Γ : Con Term n) (k l B : Term n) : Set where
    inductive
    constructor [~]
    field
      A     : Term n
      D     : Γ ⊢ A ⇒* B
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑ A

  -- Type equality.
  record _⊢_[conv↑]_ (Γ : Con Term n) (A B : Term n) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term n
      D      : Γ ⊢ A ⇒* A′
      D′     : Γ ⊢ B ⇒* B′
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_ (Γ : Con Term n) : (A B : Term n) → Set where
    U-refl     : ⊢ Γ → Γ ⊢ U [conv↓] U
    ℕ-refl     : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ
    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty
    Unit-refl  : ⊢ Γ → Γ ⊢ Unit [conv↓] Unit
    ne         : ∀ {K L}
               → Γ ⊢ K ~ L ↓ U
               → Γ ⊢ K [conv↓] L
    Π-cong     : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → Γ ⊢ Π F ▹ G [conv↓] Π H ▹ E
    Σ-cong     : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → Γ ⊢ Σ F ▹ G [conv↓] Σ H ▹ E

  -- Term equality.
  record _⊢_[conv↑]_∷_ (Γ : Con Term n) (t u A : Term n) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term n
      D       : Γ ⊢ A ⇒* B
      d       : Γ ⊢ t ⇒* t′ ∷ B
      d′      : Γ ⊢ u ⇒* u′ ∷ B
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_ (Γ : Con Term n) : (t u A : Term n) → Set where
    ℕ-ins     : ∀ {k l}
              → Γ ⊢ k ~ l ↓ ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ
    Empty-ins : ∀ {k l}
              → Γ ⊢ k ~ l ↓ Empty
              → Γ ⊢ k [conv↓] l ∷ Empty
    Unit-ins  : ∀ {k l}
              → Γ ⊢ k ~ l ↓ Unit
              → Γ ⊢ k [conv↓] l ∷ Unit
    ne-ins    : ∀ {k l M N}
              → Γ ⊢ k ∷ N
              → Γ ⊢ l ∷ N
              → Neutral N
              → Γ ⊢ k ~ l ↓ M
              → Γ ⊢ k [conv↓] l ∷ N
    univ      : ∀ {A B}
              → Γ ⊢ A ∷ U
              → Γ ⊢ B ∷ U
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A [conv↓] B ∷ U
    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ
    η-eq      : ∀ {f g F G}
              → Γ ⊢ f ∷ Π F ▹ G
              → Γ ⊢ g ∷ Π F ▹ G
              → Function f
              → Function g
              → Γ ∙ F ⊢ wk1 f ∘ var x0 [conv↑] wk1 g ∘ var x0 ∷ G
              → Γ ⊢ f [conv↓] g ∷ Π F ▹ G
    Σ-η       : ∀ {p r F G}
              → Γ ⊢ p ∷ Σ F ▹ G
              → Γ ⊢ r ∷ Σ F ▹ G
              → Product p
              → Product r
              → Γ ⊢ fst p [conv↑] fst r ∷ F
              → Γ ⊢ snd p [conv↑] snd r ∷ G [ fst p ]
              → Γ ⊢ p [conv↓] r ∷ Σ F ▹ G
    η-unit    : ∀ {k l}
              → Γ ⊢ k ∷ Unit
              → Γ ⊢ l ∷ Unit
              → Whnf k
              → Whnf l
              → Γ ⊢ k [conv↓] l ∷ Unit

star-refl : ⊢ Γ → Γ ⊢ star [conv↓] star ∷ Unit
star-refl ⊢Γ = η-unit (starⱼ ⊢Γ) (starⱼ ⊢Γ) starₙ starₙ
