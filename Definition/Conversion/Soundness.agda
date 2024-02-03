{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Soundness where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

abstract mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑ : ∀ {k l A} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  soundness~↑ (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _) x≡y (refl x)
  soundness~↑ (app-cong k~l x₁) = app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑ (fst-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst-cong ⊢F ⊢G p≡
  soundness~↑ (snd-cong x) =
    let p≡ = soundness~↓ x
        ⊢ΣFG = proj₁ (syntacticEqTerm p≡)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd-cong ⊢F ⊢G p≡
  soundness~↑ (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓ k~l)
  soundness~↑ (cases-cong {A = A} {B = B} {C} {C′} ⊢C ⊢t ⊢u ⊢v) =
    cases-cong (proj₁ (syntactic∪ (proj₁ (syntacticEqTerm (soundness~↓ ⊢t)))))
               (proj₂ (syntactic∪ (proj₁ (syntacticEqTerm (soundness~↓ ⊢t)))))
               (soundnessConv↑ ⊢C)
               (soundness~↓ ⊢t)
               (soundnessConv↑Term ⊢u)
               (soundnessConv↑Term ⊢v)
  soundness~↑ (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (soundnessConv↑ x₁) (soundness~↓ k~l)

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓ : ∀ {k l A} → Γ ⊢ k ~ l ↓ A → Γ ⊢ k ≡ l ∷ A
  soundness~↓ ([~] A₁ D whnfA k~l) = conv (soundness~↑ k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B} → Γ ⊢ A [conv↑] B → Γ ⊢ A ≡ B
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B} → Γ ⊢ A [conv↓] B → Γ ⊢ A ≡ B
  soundnessConv↓ (U-refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (Unit-refl ⊢Γ) = refl (Unitⱼ ⊢Γ)
  soundnessConv↓ (ne x) = univ (soundness~↓ x)
  soundnessConv↓ (Π-cong F c c₁) =
    Π-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)
  soundnessConv↓ (Σ-cong F c c₁) =
    Σ-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)
  soundnessConv↓ (∪-cong c c₁) =
    ∪-cong (soundnessConv↑ c) (soundnessConv↑ c₁)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A} → Γ ⊢ a [conv↓] b ∷ A → Γ ⊢ a ≡ b ∷ A
  soundnessConv↓Term (ℕ-ins x) = soundness~↓ x
  soundnessConv↓Term (Empty-ins x) = soundness~↓ x
  soundnessConv↓Term (Unit-ins x) = soundness~↓ x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓ x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓ x₁) M≡A
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↓ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq x x₁ y y₁ c) =
    let ⊢ΠFG = syntacticTerm x
        ⊢F , _ = syntacticΠ ⊢ΠFG
    in  η-eq ⊢F x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    let ⊢ΣFG = syntacticTerm ⊢p
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        fst≡ = soundnessConv↑Term fstConv
        snd≡ = soundnessConv↑Term sndConv
    in  Σ-η ⊢F ⊢G ⊢p ⊢r fst≡ snd≡
  soundnessConv↓Term (∪₁-η ⊢p ⊢r injlₙ injlₙ cnv) =
    let ⊢∪AB    = syntacticTerm ⊢p
        ⊢A , ⊢B = syntactic∪ ⊢∪AB
        p≡ = soundnessConv↑Term cnv
    in  injl-cong ⊢A ⊢B p≡
  soundnessConv↓Term (∪₂-η ⊢p ⊢r injrₙ injrₙ cnv) =
    let ⊢∪AB    = syntacticTerm ⊢p
        ⊢A , ⊢B = syntactic∪ ⊢∪AB
        p≡ = soundnessConv↑Term cnv
    in  injr-cong ⊢A ⊢B p≡
  soundnessConv↓Term (∪₃-η c₁ c₂ p~r) =
    let a≡b  = soundness~↓ p~r
        ⊢A∪B = proj₁ (syntacticEqTerm a≡b)
        ⊢A   = proj₁ (syntactic∪ ⊢A∪B)
        ⊢B   = proj₂ (syntactic∪ ⊢A∪B)
    in  conv a≡b (∪-cong c₁ c₂) --( (refl ⊢A) (refl ⊢B))
 --conv a≡b (∪-cong (sym (soundnessConv↑ c₁)) (sym (soundnessConv↑ c₂)))
  soundnessConv↓Term (η-unit [a] [b] aUnit bUnit) = η-unit [a] [b]
