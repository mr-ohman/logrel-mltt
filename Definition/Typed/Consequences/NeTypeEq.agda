{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.NeTypeEq where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Inversion

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R T} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
varTypeEq′ here here = PE.refl
varTypeEq′ (there n∷R) (there n∷T) rewrite varTypeEq′ n∷R n∷T = PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
varTypeEq A B x∷A x∷B rewrite varTypeEq′ x∷A x∷B = refl A

-- The same neutral term have equal types.
neTypeEq : ∀ {t A B} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = let w = proj₂ (injectivity q)
          in  substTypeEq w (refl t∷A₁)
neTypeEq (fstₙ neP) (fstⱼ ⊢F ⊢G ⊢t) (fstⱼ ⊢F′ ⊢G′ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = proj₁ (Σ-injectivity q)
neTypeEq (sndₙ neP) (sndⱼ ⊢F ⊢G ⊢t) (sndⱼ ⊢F′ ⊢G′ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = let G≡G₁ = proj₂ (Σ-injectivity q)
              ⊢fst = fstⱼ ⊢F ⊢G ⊢t
          in  substTypeEq G≡G₁ (refl ⊢fst)
neTypeEq (natrecₙ neT) (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
neTypeEq (Emptyrecₙ neT) (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq (casesₙ neT) (casesⱼ ⊢t ⊢u ⊢v ⊢C) (casesⱼ ⊢t₁ ⊢u₁ ⊢v₁ ⊢C₁) =
  refl ⊢C
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃

{--
typeEq▹▹ : ∀ {t A B C} → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B ▹▹ C → Γ ⊢ A ≡ B ▹▹ C
typeEq▹▹ (Πⱼ ⊢t₁ ▹ ⊢t₃) ⊢t₂ = {!!}
typeEq▹▹ (Σⱼ ⊢t₁ ▹ ⊢t₃) ⊢t₂ = {!!}
typeEq▹▹ (⊢t₁ ∪ⱼ ⊢t₃) ⊢t₂ = {!!}
typeEq▹▹ (ℕⱼ x) ⊢t₂ = {!!}
typeEq▹▹ (Emptyⱼ x) ⊢t₂ = {!!}
typeEq▹▹ (Unitⱼ x) ⊢t₂ = {!!}
typeEq▹▹ (var x x₁) ⊢t₂ = {!!}
typeEq▹▹ (lamⱼ x ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (⊢t₁ ∘ⱼ ⊢t₃) ⊢t₂ = {!!}
typeEq▹▹ (prodⱼ x x₁ ⊢t₁ ⊢t₃) ⊢t₂ = {!!}
typeEq▹▹ (fstⱼ x x₁ ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (sndⱼ x x₁ ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (injlⱼ ⊢t₁ x) ⊢t₂ = {!!}
typeEq▹▹ (injrⱼ x ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (casesⱼ ⊢t₁ ⊢t₃ ⊢t₄ x) ⊢t₂ = {!!}
typeEq▹▹ (zeroⱼ x) ⊢t₂ = {!!}
typeEq▹▹ (sucⱼ ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (natrecⱼ x ⊢t₁ ⊢t₃ ⊢t₄) ⊢t₂ = {!!}
typeEq▹▹ (Emptyrecⱼ x ⊢t₁) ⊢t₂ = {!!}
typeEq▹▹ (starⱼ x) ⊢t₂ = {!!}
typeEq▹▹ (conv ⊢t₁ x) ⊢t₂ = {!!}
--}

typeEqVar : ∀ {x A B}
          → x ∷ A ∈ Γ
          → Γ ⊢ var x ∷ B
          → Γ ⊢ A ≡ B
typeEqVar {_} {_} {x} {A} {B} i ⊢x@(var x₁ x₂) rewrite varTypeEq′ i x₂ = refl (syntacticTerm ⊢x)
typeEqVar {_} {_} {x} {A} {B} i (conv ⊢x x₁) = trans (typeEqVar i ⊢x) x₁

{--
-- Not true when t is injl for example. We have
--   injl zero ∷ ℕ ∪ Unit
--   injl zero ∷ ℕ ∪ Empty
-- We could require that injections carry the "missing" type
typeEq : ∀ {t A B} → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
typeEq (Πⱼ ⊢t₁ ▹ ⊢t₃) ⊢t₂ with inversion-Π ⊢t₂
... | a , b , c = sym c
typeEq (Σⱼ ⊢t₁ ▹ ⊢t₃) ⊢t₂ with inversion-Σ ⊢t₂
... | a , b , c = sym c
typeEq (⊢t₁ ∪ⱼ ⊢t₃) ⊢t₂ with inversion-∪ ⊢t₂
... | a , b , c = sym c
typeEq (ℕⱼ x) ⊢t₂ = sym (inversion-ℕ ⊢t₂)
typeEq (Emptyⱼ x) ⊢t₂ = sym (inversion-Empty ⊢t₂)
typeEq (Unitⱼ x) ⊢t₂ = sym (inversion-Unit ⊢t₂)
typeEq (var x x₁) ⊢t₂ = typeEqVar x₁ ⊢t₂
typeEq (lamⱼ {F} {G} {t} x ⊢t₁) ⊢t₂ with inversion-lam ⊢t₂
... | F₁ , G₁ , ⊢F₁ , ⊢G₁ , ⊢≡ =
  {!the problem is that lam is untyped so nothing constrains F and F₁ to be the same!}
 --sym (trans ⊢≡ (Π-cong ⊢F {!!} {!!}))
typeEq (_∘ⱼ_ {g} {a} {F} {G} ⊢t₁ ⊢t₃) ⊢t₂ with inversion-app ⊢t₂
... | F₁ , G₁ , ⊢g , ⊢a , ⊢≡ =
  trans (substTypeEq {_} {_} {a} {a} {F} {G} {G₁} {!!} {!!}) (sym ⊢≡)
typeEq (prodⱼ x x₁ ⊢t₁ ⊢t₃) ⊢t₂ = {!!}
typeEq (fstⱼ x x₁ ⊢t₁) ⊢t₂ = {!!}
typeEq (sndⱼ x x₁ ⊢t₁) ⊢t₂ = {!!}
typeEq (injlⱼ {A} {B} ⊢t₁ x) ⊢t₂ with inversion-injl ⊢t₂
... | A₁ , B₁ , ⊢t , ⊢≡ = trans (∪-cong (typeEq ⊢t₁ ⊢t) {!we can't know that!}) (sym ⊢≡)
typeEq (injrⱼ x ⊢t₁) ⊢t₂ = {!!}
typeEq (casesⱼ ⊢t₁ ⊢t₃ ⊢t₄ x) ⊢t₂ = {!!}
typeEq (zeroⱼ x) ⊢t₂ = sym (inversion-zero ⊢t₂)
typeEq (sucⱼ ⊢t₁) ⊢t₂ = sym (proj₂ (inversion-suc ⊢t₂))
typeEq (natrecⱼ x ⊢t₁ ⊢t₃ ⊢t₄) ⊢t₂ = {!!}
typeEq (Emptyrecⱼ x ⊢t₁) ⊢t₂ = {!Empty is not inhabited!}
typeEq (starⱼ x) ⊢t₂ = sym (inversion-star ⊢t₂)
typeEq (conv ⊢t₁ x) ⊢t₂ = trans (sym x) (typeEq ⊢t₁ ⊢t₂)
--}
