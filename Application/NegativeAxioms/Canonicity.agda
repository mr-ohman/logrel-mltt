-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

{-# OPTIONS --without-K --safe #-}

module Application.NegativeAxioms.Canonicity where

open import Definition.Untyped as U

open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T
open import Definition.Typed.Consequences.Inequality
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Syntactic

open import Definition.Conversion.Consequences.Completeness
open import Definition.Conversion.FullReduction

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m m'  : Nat
    x     : Fin m
    ρ     : Wk m m'
    σ     : Subst m m'
    Γ Δ   : Con Term m
    A B C : Term m
    t u   : Term m

-- Numerals

data Numeral {m : Nat} : Term m → Set where
  zeroₙ : Numeral zero
  sucₙ  : Numeral t → Numeral (suc t)

-- Negative types
---------------------------------------------------------------------------

-- A type is negative if all of its branches end in ⊥.
-- The prime example is negation ¬A.

data NegativeType (Γ : Cxt m) : Ty m → Set where

  empty : NegativeType Γ Empty

  pi    : Γ ⊢ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Π A ▹ B)

  sigma : Γ ⊢ A
        → NegativeType Γ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Σ A ▹ B)

  conv  : NegativeType Γ A
        → Γ ⊢ A ≡ B
        → NegativeType Γ B

-- Lemma: Negative types are closed under weakening.

wkNeg : ρ ∷ Δ ⊆ Γ → ⊢ Δ → NegativeType Γ A → NegativeType Δ (U.wk ρ A)

wkNeg w ⊢Δ empty
  = empty

wkNeg w ⊢Δ (pi dA nB)
  = pi dA' (wkNeg (lift w) (⊢Δ ∙ dA') nB)
    where dA' = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (sigma dA nA nB)
  = sigma dA' (wkNeg w ⊢Δ nA) (wkNeg (lift w) (⊢Δ ∙ dA') nB)
    where dA' = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (conv n c)
  = conv (wkNeg w ⊢Δ n) (wkEq w ⊢Δ c)

-- Lemma: Negative types are closed under parallel substitution.

subNeg : NegativeType Γ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → NegativeType Δ (subst σ A)

subNeg empty _ _ = empty

subNeg (pi ⊢A n) s ⊢Δ
  = pi ⊢σA (subNeg n (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
    where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (sigma ⊢A nA nB) s ⊢Δ
  = sigma ⊢σA (subNeg nA s ⊢Δ) (subNeg nB (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
    where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (conv n c) s ⊢Δ = conv (subNeg n s ⊢Δ) (substitutionEq c (substRefl s) ⊢Δ)

-- Corollary: Negative types are closed under single substitution.

subNeg1 : NegativeType (Γ ∙ A) B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
subNeg1 n ⊢t = subNeg n (singleSubst ⊢t) (wfTerm ⊢t)

-- Lemma: The first component of a negative Σ-type is negative.

fstNeg : NegativeType Γ C → Γ ⊢ C ≡ Σ A ▹ B → NegativeType Γ A
fstNeg empty          c = ⊥-elim (Empty≢Σⱼ c)
fstNeg (pi _ _)       c = ⊥-elim (Π≢Σ c)
fstNeg (sigma _ nA _) c = conv nA (proj₁ (Σ-injectivity c))
fstNeg (conv n c)    c' = fstNeg n (trans c c')

-- Lemma: Any instance of the second component of a negative Σ-type is negative.

sndNeg : NegativeType Γ C → Γ ⊢ C ≡ Σ A ▹ B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
sndNeg empty          c = ⊥-elim (Empty≢Σⱼ c)
sndNeg (pi _ _)       c = ⊥-elim (Π≢Σ c)
sndNeg (sigma _ _ nB) c ⊢t = let (cA , cB) = Σ-injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
sndNeg (conv n c)    c' = sndNeg n (trans c c')

-- Lemma: Any instance of the codomain of a negative Π-type is negative.

appNeg : NegativeType Γ C → Γ ⊢ C ≡ Π A ▹ B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
appNeg empty          c = ⊥-elim (Empty≢Πⱼ c)
appNeg (sigma _ _ _)  c = ⊥-elim (Π≢Σ (sym c))
appNeg (pi _ nB) c ⊢t = let (cA , cB) = injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
appNeg (conv n c)    c' = appNeg n (trans c c')

-- Lemma: The type ℕ is not negative.

¬negℕ : NegativeType Γ C → Γ ⊢ C ≡ ℕ → ⊥
¬negℕ empty         c = ℕ≢Emptyⱼ (sym c)
¬negℕ (pi _ _)      c = ℕ≢Π (sym c)
¬negℕ (sigma _ _ _) c = ℕ≢Σ (sym c)
¬negℕ (conv n c)   c' = ¬negℕ n (trans c c')

-- Negative contexts
---------------------------------------------------------------------------

-- A context is negative if all of its type entries are negative.

data NegativeContext : Con Ty m → Set where
  ε   : NegativeContext ε
  _∙_ : NegativeContext Γ → NegativeType Γ A → NegativeContext (Γ ∙ A)

-- Lemma: Any entry in negative context is a negative type (needs weakening).

lookupNegative : ⊢ Γ → NegativeContext Γ → (x ∷ A ∈ Γ) → NegativeType Γ A
lookupNegative ⊢Γ∙A            (nΓ ∙ nA) here
  = wkNeg (step id) ⊢Γ∙A nA
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓ ∙ nA) (there h)
  = wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓ h)

-- Main results
---------------------------------------------------------------------------

-- We assume a negative, consistent context.

module Main (nΓ : NegativeContext Γ) (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥) where

  -- Lemma: A neutral has negative type in a consistent negative context.

  neNeg : (d : Γ ⊢ u ∷ A) (n : NfNeutral u) → NegativeType Γ A
  neNeg (var ⊢Γ h       ) (var _           ) = lookupNegative ⊢Γ nΓ h
  neNeg (d ∘ⱼ ⊢t        ) (∘ₙ n _          ) = appNeg (neNeg d n) (refl (syntacticTerm d)) ⊢t
  neNeg (fstⱼ ⊢A A⊢B d  ) (fstₙ n          ) = fstNeg (neNeg d n) (refl (Σⱼ ⊢A ▹ A⊢B))
  neNeg (sndⱼ ⊢A A⊢B d  ) (sndₙ n          ) = sndNeg (neNeg d n) (refl (Σⱼ ⊢A ▹ A⊢B)) (fstⱼ ⊢A A⊢B d)
  neNeg (natrecⱼ _ _ _ d) (natrecₙ _ _ _ n ) = ⊥-elim (¬negℕ (neNeg d n) ⊢ℕ) where ⊢ℕ = refl (ℕⱼ (wfTerm d))
  neNeg (Emptyrecⱼ _ d  ) (Emptyrecₙ _ _   ) = ⊥-elim (consistent d)
  neNeg (conv d c       ) n                  = conv (neNeg d n) c

  -- Lemma: A normal form of type ℕ is a numeral in a consistent negative context.

  nfN : (d : Γ ⊢ u ∷ A)
      → (n : Nf u)
      → (c : Γ ⊢ A ≡ ℕ)
      → Numeral u

  -- Case: neutrals. The type cannot be ℕ since it must be negative.
  nfN d (ne n) c = ⊥-elim (¬negℕ (neNeg d n) c)

  -- Case: numerals.
  nfN (zeroⱼ x) zeroₙ   c = zeroₙ
  nfN (sucⱼ d) (sucₙ n) c = sucₙ (nfN d n c)

  -- Case: conversion.
  nfN (conv d c) n c' = nfN d n (trans c c')

  -- Impossible cases: type is not ℕ.

  -- * Canonical types
  nfN (Πⱼ _ ▹ _)      (Πₙ _ _)    c = ⊥-elim (U≢ℕ c)
  nfN (Σⱼ _ ▹ _)      (Σₙ _ _)    c = ⊥-elim (U≢ℕ c)
  nfN (ℕⱼ _)           ℕₙ         c = ⊥-elim (U≢ℕ c)
  nfN (Emptyⱼ _)       Emptyₙ     c = ⊥-elim (U≢ℕ c)
  nfN (Unitⱼ _)        Unitₙ      c = ⊥-elim (U≢ℕ c)

  -- * Canonical forms
  nfN (lamⱼ _ _)      (lamₙ _)    c = ⊥-elim (ℕ≢Π (sym c))
  nfN (prodⱼ _ _ _ _) (prodₙ _ _) c = ⊥-elim (ℕ≢Σ (sym c))
  nfN (starⱼ _)       starₙ       c = ⊥-elim (ℕ≢Unitⱼ (sym c))
  -- q.e.d


  -- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

  thm : (⊢t : Γ ⊢ t ∷ ℕ) → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ

  thm ⊢t with fullRedTerm (completeEqTerm (refl ⊢t))
  ... | u , nf , eq = u , nfN (proj₂ (proj₂ (syntacticEqTerm eq))) nf (refl (ℕⱼ (wfTerm ⊢t))) , eq

-- Q.E.D. 2021-05-27
