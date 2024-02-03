{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Conversion where

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Whnf using (ne~↑ ; ne~↓)
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n

{--
Whnf≡ : {A B A′ : Term n}
      → Γ ⊢ A ≡ B
      → Γ ⊢ A ⇒* A′
      → Whnf A′
      → ∃ (λ B′ → Whnf B′ × Γ ⊢ B ⇒* B′ × Γ ⊢ A′ ≡ B′)
Whnf≡ {A} {B} {A′} ⊢≡ ⊢⇒ nf = {!!}

-- We would need to derive from (Γ ⊢ B ≡ C) and (Γ ⊢ B ⇒* A′) and (Whnf A′)
-- that there exists a C′ such that (Whnf C′) and (Γ ⊢ C ⇒* C′) and (Γ ⊢ A′ ≡ C′)
convConv↑ : ∀ {A B C D}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ A ≡ B
          → Γ ⊢ C ≡ D
          → Γ ⊢ A [conv↑] C
          → Δ ⊢ B [conv↑] D
convConv↑ {Γ = Γ} {Δ = Δ} {A} {B} {C} {D} ⊢Γ ⊢A ⊢C ([↑] A′ B′ D₁ D′ whnfA′ whnfB′ A′<>B′)
  with Whnf≡ ⊢A D₁ whnfA′ | Whnf≡ ⊢C D′ whnfB′
... | X , wX , ⇒X , ≡X | Y , wY , ⇒Y , ≡Y =
  [↑] X Y {!⇒X!} {!⇒Y!} wX wY {!!}
 --[↑] {!!} {!!} {!!} {!!} {!!} {!!} {!!}

-- Is that provable?
-- ∀ {t u A B} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ B → Γ ⊢ t ≡ u ∷ B
-- ∀ {t A B} → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B

convConv↓ : ∀ {A B C D}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ A ≡ B
          → Γ ⊢ C ≡ D
          → Whnf A
          → Whnf B
          → Whnf C
          → Whnf D
          → Γ ⊢ A [conv↓] C
          → Δ ⊢ B [conv↓] D
convConv↓ {Γ = Γ} {Δ = Δ} {.U} {B} {.U} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (U-refl x)
  rewrite U≡A ⊢A | U≡A ⊢C
  = U-refl (proj₁ (proj₂ (contextConvSubst ⊢Γ)))
convConv↓ {Γ = Γ} {Δ = Δ} {.ℕ} {B} {.ℕ} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (ℕ-refl x)
  rewrite ℕ≡A ⊢A wB | ℕ≡A ⊢C wD
  = ℕ-refl (proj₁ (proj₂ (contextConvSubst ⊢Γ)))
convConv↓ {Γ = Γ} {Δ = Δ} {.Empty} {B} {.Empty} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (Empty-refl x)
  rewrite Empty≡A ⊢A wB | Empty≡A ⊢C wD
  = Empty-refl (proj₁ (proj₂ (contextConvSubst ⊢Γ)))
convConv↓ {Γ = Γ} {Δ = Δ} {.Unit} {B} {.Unit} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (Unit-refl x)
  rewrite Unit≡A ⊢A wB | Unit≡A ⊢C wD
  = Unit-refl (proj₁ (proj₂ (contextConvSubst ⊢Γ)))
convConv↓ {Γ = Γ} {Δ = Δ} {A} {B} {C} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (ne x)
  with ne≡A (proj₁ (proj₂ (ne~↓ x))) ⊢A wB | ne≡A (proj₂ (proj₂ (ne~↓ x))) ⊢C wD
... | M , nM , PE.refl | N , nN , PE.refl =
  {!!}
convConv↓ {Γ = Γ} {Δ = Δ} {.(Π _ ▹ _)} {B} {.(Π _ ▹ _)} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (Π-cong x x₁ x₂) = {!!}
convConv↓ {Γ = Γ} {Δ = Δ} {.(Σ _ ▹ _)} {B} {.(Σ _ ▹ _)} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (Σ-cong x x₁ x₂) = {!!}
convConv↓ {Γ = Γ} {Δ = Δ} {.(_ ∪ _)} {B} {.(_ ∪ _)} {D} ⊢Γ ⊢A ⊢C wA wB wC wD (∪-cong x₁ x₂) = {!!}
--}

{--
convConv↓ {A = .U} {B = B} {C = .U} ⊢Γ ⊢A (U-refl x) = {!!}
convConv↓ {A = .ℕ} {B = B} {C = .ℕ} ⊢Γ ⊢A (ℕ-refl x) = {!!}
convConv↓ {A = .Empty} {B = B} {C = .Empty} ⊢Γ ⊢A (Empty-refl x) = {!!}
convConv↓ {A = .Unit} {B = B} {C = .Unit} ⊢Γ ⊢A (Unit-refl x) = {!!}
convConv↓ {A = A} {B = B} {C = C} ⊢Γ ⊢A (ne x) = {!!}
convConv↓ {A = .(Π _ ▹ _)} {B = B} {C = .(Π _ ▹ _)} ⊢Γ ⊢A (Π-cong x x₁ x₂) = {!!}
convConv↓ {A = .(Σ _ ▹ _)} {B = B} {C = .(Σ _ ▹ _)} ⊢Γ ⊢A (Σ-cong x x₁ x₂) = {!!}
--}

{--convConv↓ {A = .U} {B = B} {C = .U} ⊢Γ ⊢A ⊢C (U-refl x) rewrite U≡A ⊢A | U≡A ⊢C =
  U-refl (proj₁ (proj₂ (contextConvSubst ⊢Γ)))
convConv↓ {A = .ℕ} {B = B} {C = .ℕ} ⊢Γ ⊢A ⊢C (ℕ-refl x) = {!!}
--rewrite ℕ≡A ⊢A | ℕ≡A ⊢C =
--  {!!}
convConv↓ {A = .Empty} {B = B} {C = .Empty} {D = D} ⊢Γ ⊢A ⊢C (Empty-refl x) = {!!}
convConv↓ {A = .Unit} {B = B} {C = .Unit} {D = D} ⊢Γ ⊢A ⊢C (Unit-refl x) = {!!}
convConv↓ {A = A} {B = B} {C = C} {D = D} ⊢Γ ⊢A ⊢C (ne x) = {!!}
convConv↓ {A = .(Π _ ▹ _)} {B = B} {C = .(Π _ ▹ _)} {D = D} ⊢Γ ⊢A ⊢C (Π-cong x x₁ x₂) = {!!}
convConv↓ {A = .(Σ _ ▹ _)} {B = B} {C = .(Σ _ ▹ _)} {D = D} ⊢Γ ⊢A ⊢C (Σ-cong x x₁ x₂) = {!!}
--}

mutual
  -- Conversion of algorithmic equality.
  convConv↑Term : ∀ {t u A B}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] u ∷ A
                → Δ ⊢ t [conv↑] u ∷ B
  convConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  [↑]ₜ B′ t′ u′ (stabilityRed* Γ≡Δ (red D′))
             (stabilityRed*Term Γ≡Δ (conv* d B₁≡B′))
             (stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B′)) whnfB′ whnft′ whnfu′
             (convConv↓Term Γ≡Δ B₁≡B′ whnfB′ t<>u)

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term : ∀ {t u A B}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B
                → Whnf B
                → Γ ⊢ t [conv↓] u ∷ A
                → Δ ⊢ t [conv↓] u ∷ B
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (Empty-ins x) rewrite Empty≡A A≡B whnfB =
    Empty-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (Unit-ins x) rewrite Unit≡A A≡B whnfB =
    Unit-ins (stability~↓ Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           neB (stability~↓ Γ≡Δ x₁)
  convConv↓Term Γ≡Δ A≡B whnfB (univ x x₁ x₂) rewrite U≡A A≡B =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  convConv↓Term Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  convConv↓Term Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x₁ x₂ y y₁ x₃) | F′ , G′ , PE.refl =
    let F≡F′ , G≡G′ = injectivity A≡B
    in  η-eq (stabilityTerm Γ≡Δ (conv x₁ A≡B))
             (stabilityTerm Γ≡Δ (conv x₂ A≡B)) y y₁
             (convConv↑Term (Γ≡Δ ∙ F≡F′) G≡G′ x₃)
  convConv↓Term Γ≡Δ A≡B whnfB (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv)
    with Σ≡A A≡B whnfB
  ... | F , G , PE.refl =
    let F≡ , G≡ = Σ-injectivity A≡B
        ⊢F = proj₁ (syntacticEq F≡)
        ⊢G = proj₁ (syntacticEq G≡)
        ⊢fst = fstⱼ ⊢F ⊢G ⊢p
    in  Σ-η (stabilityTerm Γ≡Δ (conv ⊢p A≡B))
            (stabilityTerm Γ≡Δ (conv ⊢r A≡B))
            pProd
            rProd
            (convConv↑Term Γ≡Δ F≡ fstConv)
            (convConv↑Term Γ≡Δ (substTypeEq G≡ (refl ⊢fst)) sndConv)
  convConv↓Term Γ≡Δ A≡B whnfB (∪₁-η ⊢p ⊢r pInj rInj cnv)
    with ∪≡A A≡B whnfB
  ... | C , D , PE.refl =
    let C≡ , D≡ = ∪-injectivity A≡B
    in  ∪₁-η (stabilityTerm Γ≡Δ (conv ⊢p A≡B))
             (stabilityTerm Γ≡Δ (conv ⊢r A≡B))
             pInj rInj
             (convConv↑Term Γ≡Δ C≡ cnv)
  convConv↓Term Γ≡Δ A≡B whnfB (∪₂-η ⊢p ⊢r pInj rInj cnv)
    with ∪≡A A≡B whnfB
  ... | C , D , PE.refl =
    let C≡ , D≡ = ∪-injectivity A≡B
    in  ∪₂-η (stabilityTerm Γ≡Δ (conv ⊢p A≡B))
             (stabilityTerm Γ≡Δ (conv ⊢r A≡B))
             pInj rInj
             (convConv↑Term Γ≡Δ D≡ cnv)
  convConv↓Term Γ≡Δ A≡B whnfB (∪₃-η c₁ c₂ p~r)
    with ∪≡A A≡B whnfB
  ... | C , D , PE.refl =
    let C≡ , D≡ = ∪-injectivity A≡B
    in  ∪₃-η (stabilityEq Γ≡Δ (trans c₁ C≡))
             (stabilityEq Γ≡Δ (trans c₂ D≡))
             (stability~↓ Γ≡Δ p~r)
  convConv↓Term Γ≡Δ A≡B whnfB (η-unit [t] [u] tUnit uUnit) rewrite Unit≡A A≡B whnfB =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit [t] [u] tUnit uUnit

{--
  conv~↓ : ∀ {t u A B}
           → Whnf A
           → Whnf B
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ~ u ↓ A
           → Δ ⊢ t ~ u ↓ B
  conv~↓ {t = t} {u = u} {A = A} {B = B} whnfA whnfB Γ≡Δ A≡B ([~] A₁ D whnfB₁ k~l) =
    [~] {!!} {!!} whnfB {!!}

  -- In the app case, we would need to turn the B in Γ ⊢ G [ t ] ≡ B into a substitution
  conv~↑ : ∀ {t u A B}
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ~ u ↑ A
           → Γ ⊢ t ~ u ↑ B
  conv~↑ {t = .(var _)} {u = .(var _)} {A = A} {B = B} A≡B (var-refl x x₁) =
    var-refl (conv x A≡B) x₁
  conv~↑ {t = .(_ ∘ _)} {u = .(_ ∘ _)} {A = .(G [ z ])} {B = B} A≡B (app-cong {k} {l} {z} {w} {F} {G} x x₁) =
    let ⊢F , ⊢G = syntacticΠ (proj₁ (syntacticEqTerm (soundness~↓ x)))
        -- Can we prove?
        --   Γ · F ⊢ G → Γ ⊢ G [ t ] ≡ B → ∃ (λ H → B PE.≡ H [ t ] × Γ · F ⊢ G ≡ H)
    in  {!app-cong!}
  conv~↑ {t = .(fst _)} {u = .(fst _)} {A = A} {B = B} A≡B (fst-cong x) =
    let ⊢F , ⊢G = syntacticΣ (proj₁ (syntacticEqTerm (soundness~↓ x)))
    in  fst-cong (conv~↓ Σₙ Σₙ (reflConEq (wfEq A≡B)) (Σ-cong ⊢F A≡B (refl ⊢G)) x)
  conv~↑ {t = .(snd _)} {u = .(snd _)} {A = .(G [ fst p ])} {B = B} A≡B (snd-cong {p} {r} {F} {G} x) =
    {!!}
  conv~↑ {t = .(natrec _ _ _ _)} {u = .(natrec _ _ _ _)} {A = .(F [ k ])} {B = B} A≡B (natrec-cong {k} {l} {h} {g} {a₀} {b₀} {F} {G} x x₁ x₂ x₃) =
    {!!}
  conv~↑ {t = .(cases A _ _ _)} {u = .(cases _ _ _ _)} {A = A} {B = B} A≡B (cases-cong x x₁ x₂ x₃) =
    {!!}
  conv~↑ {t = .(Emptyrec A _)} {u = .(Emptyrec _ _)} {A = A} {B = B} A≡B (Emptyrec-cong x x₁) =
    {!!}
--}

-- Conversion of algorithmic equality with the same context.
abstract
  convConvTerm : ∀ {t u A B}
               → Γ ⊢ t [conv↑] u ∷ A
               → Γ ⊢ A ≡ B
               → Γ ⊢ t [conv↑] u ∷ B
  convConvTerm t<>u A≡B = convConv↑Term (reflConEq (wfEq A≡B)) A≡B t<>u
