module Tools.HeterogeneousEquality where

import Tools.PropositionalEquality as PE


infix 4 _≅_

data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

≅-to-≡ : {A : Set} {x y : A} → x ≅ y → x PE.≡ y
≅-to-≡ refl = PE.refl

≡-to-≅ : {A : Set} {x y : A} → x PE.≡ y → x ≅ y
≡-to-≅ PE.refl = refl

sym : ∀ {A B : Set} {a : A} {b : B} → a ≅ b → b ≅ a
sym refl = refl

trans : ∀ {A B C : Set} {a : A} {b : B} {c : C} → a ≅ b → b ≅ c → a ≅ c
trans refl refl = refl

cong : ∀ {A : Set} {B : A → Set} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

cong₂ : ∀ {A : Set} {B : A → Set} {C : ∀ x → B x → Set}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂ f refl refl = refl

≡-subst-removable : ∀ {A : Set}
                    (P : A → Set) {x y} (eq : x PE.≡ y) z →
                    PE.subst P eq z ≅ z
≡-subst-removable P PE.refl z = refl
