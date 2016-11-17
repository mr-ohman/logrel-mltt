module Tools.PropositionalEquality where


open import Agda.Builtin.Equality public
open import Tools.Empty

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
a ≢ b = a ≡ b → ⊥

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : ∀ {A B C : Set} {a a' b b'}
        (f : A → B → C) → a ≡ a' → b ≡ b'
      → f a b ≡ f a' b'
cong₂ f refl refl = refl

cong₃ : ∀ {A B C D : Set} {a a' b b' c c'}
        (f : A → B → C → D) → a ≡ a' → b ≡ b' → c ≡ c'
      → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} {a a' b b' c c' d d'}
        (f : A → B → C → D → E) → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d'
      → f a b c d ≡ f a' b' c' d'
cong₄ f refl refl refl refl = refl

subst : {A : Set} {a b : A} (F : A → Set) → a ≡ b → F a → F b
subst F refl f = f

subst₂ : ∀ {A B : Set} {a a' b b'} (F : A → B → Set)
       → a ≡ a' → b ≡ b' → F a b → F a' b'
subst₂ F refl refl f = f
