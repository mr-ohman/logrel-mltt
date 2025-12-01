{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function


-- Judgmental instance of the equality relation

instance eqRelInstance : EqRelSet
eqRelInstance = record {
  _⊢_≅_ = _⊢_≡_;
  _⊢_≅_∷_ = _⊢_≡_∷_;
  _⊢_~_∷_ = _⊢_≡_∷_;
  ~-to-≅ₜ = idᶠ;
  ≅-eq = idᶠ;
  ≅ₜ-eq = idᶠ;
  ≅-univ = univ;
  ≅-sym = sym;
  ≅ₜ-sym = sym;
  ~-sym = sym;
  ≅-trans = trans;
  ≅ₜ-trans = trans;
  ~-trans = trans;
  ≅-conv = conv;
  ~-conv = conv;
  ≅-wk = wkEq;
  ≅ₜ-wk = wkEqTerm;
  ~-wk = wkEqTerm;
  ≅-red = reduction;
  ≅ₜ-red = reductionₜ;
  ≅-Urefl = refl ∘ᶠ Uⱼ;
  ≅-ℕrefl = refl ∘ᶠ ℕⱼ;
  ≅ₜ-ℕrefl = refl ∘ᶠ ℕⱼ;
  ≅-Emptyrefl = refl ∘ᶠ Emptyⱼ;
  ≅ₜ-Emptyrefl = refl ∘ᶠ Emptyⱼ;
  ≅-Unitrefl = refl ∘ᶠ Unitⱼ;
  ≅ₜ-Unitrefl = refl ∘ᶠ Unitⱼ;
  ≅ₜ-η-unit = η-unit;
  ≅-Π-cong = Π-cong;
  ≅ₜ-Π-cong = Π-cong;
  ≅-Σ-cong = Σ-cong;
  ≅ₜ-Σ-cong = Σ-cong;
  ≅-∪-cong = ∪-cong;
  ≅ₜ-∪-cong = ∪-cong;
  ≅-injl-cong = injl-cong;
  ≅-injr-cong = injr-cong;
  ≅-∥-cong = ∥-cong;
  ≅ₜ-∥-cong = ∥-cong;
  ≅-∥ᵢ-cong = ∥ᵢ-cong;
  ≅ₜ-zerorefl = refl ∘ᶠ zeroⱼ;
  ≅-suc-cong = suc-cong;
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅;
  ≅-Σ-η = λ ⊢F ⊢G ⊢p ⊢r pProd rProd fst≡ snd≡ → Σ-η ⊢F ⊢G ⊢p ⊢r fst≡ snd≡;
  ~-var = refl;
  ~-app = app-cong;
  ~-fst = fst-cong;
  ~-snd = snd-cong;
  ~-natrec = natrec-cong;
  ~-cases = cases-cong;
  ~-∥ₑ = ∥ₑ-cong;
  ~-Emptyrec = Emptyrec-cong }
