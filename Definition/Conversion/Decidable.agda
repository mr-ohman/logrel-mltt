{-# OPTIONS --without-K --safe --lossy-unification #-}

module Definition.Conversion.Decidable where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
  using (wfEqTerm ; whrDet* ; wf ; whrDet*Term)
open import Definition.Typed.Weakening
  using (▹▹-cong)
open import Definition.Conversion
open import Definition.Conversion.Whnf
  using (ne~↓ ; whnfConv↓Term)
open import Definition.Conversion.Soundness
  using (soundness~↓ ; soundnessConv↓Term ; soundnessConv↑ ; soundness~↑ ; soundnessConv↓ ; soundnessConv↑Term)
open import Definition.Conversion.Symmetry
  using (symConv↓Term′)
open import Definition.Conversion.Stability
  using (⊢_≡_ ; stability~↑ ; symConEq ; stabilityConv↑ ; reflConEq ; stabilityConv↑Term ; _∙_)
open import Definition.Conversion.Conversion
  using (convConvTerm)
open import Definition.Conversion.PreDecidable

open import Definition.Typed.Consequences.Syntactic
  using (syntacticEqTerm ; syntacticEq ; syntacticΣ ; syntactic∪ ; syntacticTerm)
open import Definition.Typed.Consequences.Substitution
  using (substTypeEq)
open import Definition.Typed.Consequences.Injectivity
  using (injectivity ; ∪-injectivity)
open import Definition.Typed.Consequences.Reduction
  using (whNorm)
open import Definition.Typed.Consequences.Equality
  using (Π≡A ; Σ≡A ; ℕ≡A ; Empty≡A ; U≡A ; ∪≡A)
open import Definition.Typed.Consequences.Inequality as IE
  using ()
open import Definition.Typed.Consequences.NeTypeEq
  using (neTypeEq)
open import Definition.Typed.Consequences.SucCong
  using (sucCong)

open import Tools.Fin
  using (_≟ⱽ_)
open import Tools.Nat
  using (Nat)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Nat
    Γ Δ : Con Term ℓ

mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑ : ∀ {k l R T}
        → Γ ⊢ k ~ k ↑ R → Γ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var-refl {n} x₂ x≡y) (var-refl {m} x₃ x≡y₁) with n ≟ⱽ m
  ... | yes PE.refl = yes (_ , var-refl x₂ x≡y₁)
  ... | no ¬p = no (λ { (A , k~l) → ¬p (strongVarEq k~l) })
  dec~↑ (var-refl x₁ x≡y) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (cases-cong ⊢C ⊢t ⊢u ⊢v) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })

  dec~↑ (app-cong x x₁) (app-cong x₂ x₃)
        with dec~↓ x x₂
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓ x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓ x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL ⊢l₂ ⊢l
        F≡F′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
    in  dec~↑-app ⊢l₁ ⊢l₂ k~l (decConv↑TermConv F≡F′ x₁ x₃)
  ... | no ¬p = no (λ { (_ , app-cong x₄ x₅) → ¬p (_ , x₄) })
  dec~↑ (app-cong x₁ x₂) (var-refl x₃ x≡y) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (cases-cong ⊢C ⊢t ⊢u ⊢v) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })

  dec~↑ (fst-cong {k} k~k) (fst-cong {l} l~l) with dec~↓ k~k l~l
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
        ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
        F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
    in  yes (F , fst-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                          A≡ΣFG
                          k~l))
  ... | no ¬p = no (λ { (_ , fst-cong x₂) → ¬p (_ , x₂) })
  dec~↑ (fst-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (snd-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (cases-cong ⊢C ⊢t ⊢u ⊢v) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })

  dec~↑ (snd-cong {k} k~k) (snd-cong {l} l~l) with dec~↓ k~k l~l
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
        ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
        F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
    in  yes (G [ fst k ] , snd-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                                    A≡ΣFG
                                    k~l))
  ... | no ¬p = no (λ { (_ , snd-cong x₂) → ¬p (_ , x₂) })
  dec~↑ (snd-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (fst-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (cases-cong ⊢C ⊢t ⊢u ⊢v) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })

  dec~↑ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        with decConv↑ x x₄
  ... | yes p
        with decConv↑TermConv
               (substTypeEq (soundnessConv↑ p)
                            (refl (zeroⱼ (wfEqTerm (soundness~↓ x₃)))))
               x₁ x₅
           | decConv↑TermConv (sucCong (soundnessConv↑ p)) x₂ x₆
           | dec~↓ x₃ x₇
  ... | yes p₁ | yes p₂ | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x₃)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
    in  yes (_ , natrec-cong p p₁ p₂ k~l′)
  ... | yes p₁ | yes p₂ | no ¬p =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p (_ , x₁₁) })
  ... | yes p₁ | no ¬p | r =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₁₀ })
  ... | no ¬p | w | r =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₉ })
  dec~↑ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
    | no ¬p = no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₈ })
  dec~↑ (natrec-cong _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (cases-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (Emptyrec-cong _ _) = no (λ { (_ , ()) })

  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (var-refl x x₁) = no (λ { (_ , ()) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (app-cong x x₁) = no (λ { (_ , ()) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (fst-cong x) = no (λ { (_ , ()) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (snd-cong x) = no (λ { (_ , ()) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (natrec-cong x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑ {Γ = Γ} (cases-cong {t = t} {u = u} {v = v} {A = A} {B = B} {C = R} ⊢C ⊢t ⊢u ⊢v)
        (cases-cong {t = t₁} {u = u₁} {v = v₁} {A = A₁} {B = B₁} {C = T} ⊢C′ ⊢t′ ⊢u′ ⊢v′)
    with decConv↑ ⊢C ⊢C′
  ... | yes p
    with dec~↓ ⊢t ⊢t′
  ... | yes (X , q) = c
    where
    whnfX : Whnf X
    whnfX = proj₁ (ne~↓ q)

    net : Neutral t
    net = proj₁ (proj₂ (ne~↓ q))

    net₁ : Neutral t₁
    net₁ = proj₂ (proj₂ (ne~↓ q))

    ⊢≡z₁ : Γ ⊢ X ≡ A ∪ B
    ⊢≡z₁ = neTypeEq net
                    (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ q))))
                    (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ ⊢t))))

    ⊢≡z₂ : Γ ⊢ X ≡ A₁ ∪ B₁
    ⊢≡z₂ = neTypeEq net₁
                    (proj₂ (proj₂ (syntacticEqTerm (soundness~↓ q))))
                    (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ ⊢t′))))

    ⊢≡z : Γ ⊢ A₁ ≡ A × Γ ⊢ B₁ ≡ B
    ⊢≡z = ∪-injectivity (trans (sym ⊢≡z₂) ⊢≡z₁)

    ⊢≡u : Γ ⊢ A ▹▹ R ≡ A₁ ▹▹ T
    ⊢≡u = ▹▹-cong (proj₁ (syntacticEq (sym (proj₁ ⊢≡z)))) (sym (proj₁ ⊢≡z)) (soundnessConv↑ p)

    ⊢≡v : Γ ⊢ B ▹▹ R ≡ B₁ ▹▹ T
    ⊢≡v = ▹▹-cong (proj₁ (syntacticEq (sym (proj₂ ⊢≡z)))) (sym (proj₂ ⊢≡z)) (soundnessConv↑ p)

    c : Dec (∃ (λ x → Γ ⊢ cases R t u v ~ cases T t₁ u₁ v₁ ↑ x))
    c with decConv↑TermConv ⊢≡u ⊢u ⊢u′
         | decConv↑TermConv ⊢≡v ⊢v ⊢v′
         | ∪≡A (sym ⊢≡z₁) whnfX
    c | yes r | yes s | D , E , ≡DE =
      yes (R , cases-cong p (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ≡DE q)
                            (convConvTerm r (▹▹-cong (proj₁ (syntacticEq (sym (proj₁ ⊢≡z))))
                                                     (proj₁ (∪-injectivity (sym (PE.subst (λ x → _ ⊢ x ≡ _) ≡DE ⊢≡z₁))))
                                                     (refl (proj₁ (syntacticEq (soundnessConv↑ p))))))
                            (convConvTerm s (▹▹-cong (proj₁ (syntacticEq (sym (proj₂ ⊢≡z))))
                                                     (proj₂ (∪-injectivity (sym (PE.subst (λ x → _ ⊢ x ≡ _) ≡DE ⊢≡z₁))))
                                                     (refl (proj₁ (syntacticEq (soundnessConv↑ p)))))))
    c | no r  | _     | D , E , ≡DE =
      no (λ { (_ , cases-cong x y z w) →
                 r (convConvTerm z (▹▹-cong (proj₁ (syntactic∪ (proj₁ (syntacticEqTerm (soundness~↓ y)))))
                                            (proj₁ (∪-injectivity (neTypeEq net
                                                                            (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ y))))
                                                                            (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ ⊢t)))))))
                                            (refl (proj₁ (syntacticEq (soundnessConv↑ p)))))) })
    c | _     | no s  | D , E , ≡DE =
      no (λ { (_ , cases-cong x y z w) →
                 s (convConvTerm w (▹▹-cong (proj₂ (syntactic∪ (proj₁ (syntacticEqTerm (soundness~↓ y)))))
                                            (proj₂ (∪-injectivity (neTypeEq net
                                                                            (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ y))))
                                                                            (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ ⊢t)))))))
                                            (refl (proj₁ (syntacticEq (soundnessConv↑ p)))))) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (cases-cong ⊢C′ ⊢t′ ⊢u′ ⊢v′) | yes p | no q =
    no (λ { (_ , cases-cong x y z w) → q (_ , y) })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (cases-cong ⊢C′ ⊢t′ ⊢u′ ⊢v′) | no p =
    no (λ { (_ , cases-cong x y z w) → p x })
  dec~↑ (cases-cong ⊢C ⊢t ⊢u ⊢v) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })

  dec~↑ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅)
        with decConv↑ x x₄ | dec~↓ x₁ x₅
  ... | yes p | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x₁)
        ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
        A≡Empty = Empty≡A ⊢Empty≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
    in  yes (_ , Emptyrec-cong p k~l′)
  ... | yes p | no ¬p = no (λ { (_ , Emptyrec-cong a b) → ¬p (_ , b) })
  ... | no ¬p | r = no (λ { (_ , Emptyrec-cong a b) → ¬p a })
  dec~↑ (Emptyrec-cong _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (cases-cong _ _ _ _) = no (λ { (_ , ()) })

  dec~↑′ : ∀ {k l R T}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑ R → Δ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑′ Γ≡Δ k~k l~l = dec~↑ k~k (stability~↑ (symConEq Γ≡Δ) l~l)

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓ : ∀ {k l R T}
        → Γ ⊢ k ~ k ↓ R → Γ ⊢ l ~ l ↓ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) with dec~↑ k~l k~l₁
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) | yes (B , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑ k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (red D′) whnfC k~l₂)
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) | no ¬p =
    no (λ { (A₂ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B}
           → Γ ⊢ A [conv↑] A → Γ ⊢ B [conv↑] B
           → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″)
           rewrite whrDet* (D , whnfA′) (D′ , whnfB′)
                 | whrDet* (D₁ , whnfA″) (D″ , whnfB″)
           with decConv↓ A′<>B′ A′<>B″
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | yes p =
    yes ([↑] B′ B″ D′ D″ whnfB′ whnfB″ p)
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′  = whrDet* (D₂ , whnfA‴) (D′ , whnfB′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴)
                                (D″ , whnfB″)
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y) A‴≡B′ B‴≡B″ A′<>B‴) })

  decConv↑′ : ∀ {A B}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] A → Δ ⊢ B [conv↑] B
            → Dec (Γ ⊢ A [conv↑] B)
  decConv↑′ Γ≡Δ A B = decConv↑ A (stabilityConv↑ (symConEq Γ≡Δ) B)

  -- Decidability of algorithmic equality of types in WHNF.
  decConv↓ : ∀ {A B}
           → Γ ⊢ A [conv↓] A → Γ ⊢ B [conv↓] B
           → Dec (Γ ⊢ A [conv↓] B)
  -- True cases
  decConv↓ (U-refl x) (U-refl x₁) = yes (U-refl x)
  decConv↓ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)
  decConv↓ (Empty-refl x) (Empty-refl x₁) = yes (Empty-refl x)
  decConv↓ (Unit-refl x) (Unit-refl x₁) = yes (Unit-refl x)

  -- Inspective cases
  decConv↓ (ne x) (ne x₁) with dec~↓ x x₁
  decConv↓ (ne x) (ne x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , _ = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k∷U , _ = syntacticEqTerm (soundness~↓ x)
        ⊢U≡A = neTypeEq neK ⊢k∷U ⊢k
        A≡U = U≡A ⊢U≡A
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡U k~l
    in  yes (ne k~l′)
  decConv↓ (ne x) (ne x₁) | no ¬p =
    no (λ x₂ → ¬p (U , decConv↓-ne x₂ x))

  decConv↓ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅)
           with decConv↑ x₁ x₄
  ... | yes p with decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅
  ... | yes p₁ = yes (Π-cong x p p₁)
  ... | no ¬p = no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈) → ¬p x₈ })
  decConv↓ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈) → ¬p x₇ })

  decConv↓ (Σ-cong x x₁ x₂) (Σ-cong x₃ x₄ x₅)
           with decConv↑ x₁ x₄
  ... | yes p with decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅
  ... | yes p₁ = yes (Σ-cong x p p₁)
  ... | no ¬p = no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈) → ¬p x₈ })
  decConv↓ (Σ-cong x x₁ x₂) (Σ-cong x₃ x₄ x₅) | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈) → ¬p x₇ })

  decConv↓ (∪-cong x₁ x₂) (∪-cong x₄ x₅)
    with decConv↑ x₁ x₄
  ... | yes p with decConv↑ x₂ x₅
  ... | yes q = yes (∪-cong p q)
  ... | no q = no (λ { (ne ([~] A D whnfB ())) ; (∪-cong x₇ x₈) → q x₈ })
  decConv↓ (∪-cong x₁ x₂) (∪-cong x₄ x₅) | no p =
    no (λ { (ne ([~] A D whnfB ())) ; (∪-cong x₇ x₈) → p x₇ })

  -- False cases
  decConv↓ (U-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.U≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (U-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (∪-cong x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.ℕ≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (ℕ-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (∪-cong x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Empty≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Empty-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (∪-cong x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Unit≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Unit-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (∪-cong x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ne x) (U-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.U≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (ℕ-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.ℕ≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Empty-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Empty≢neⱼ neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Unit-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Unit≢neⱼ neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Π-cong x₁ x₂ x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Π≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ (ne x) (Σ-cong x₁ x₂ x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Σ≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ (ne x) (∪-cong x₂ x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.∪≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ (Π-cong x x₁ x₂) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Σ-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (∪-cong x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Π≢ne neK (soundnessConv↓ x₄)))
  decConv↓ (Σ-cong x x₁ x₂) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (∪-cong x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Σ≢ne neK (soundnessConv↓ x₄)))
  decConv↓ (∪-cong x₁ x₂) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (Π-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (Σ-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (∪-cong x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.∪≢ne neK (soundnessConv↓ x₄)))

  -- Helper function for decidability of neutral types.
  decConv↓-ne : ∀ {A B}
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A ~ A ↓ U
              → Γ ⊢ A ~ B ↓ U
  decConv↓-ne (U-refl x) A~A = A~A
  decConv↓-ne (ℕ-refl x) A~A = A~A
  decConv↓-ne (Empty-refl x) A~A = A~A
  decConv↓-ne (ne x) A~A = x
  decConv↓-ne (Π-cong x x₁ x₂) ([~] A D whnfB ())

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A}
               → Γ ⊢ t [conv↑] t ∷ A
               → Γ ⊢ u [conv↑] u ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               rewrite whrDet* (D , whnfB) (D₁ , whnfB₁)
                     | whrDet*Term  (d , whnft′) (d′ , whnfu′)
                     | whrDet*Term  (d₁ , whnft″) (d″ , whnfu″)
               with decConv↓Term t<>u t<>u₁
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | yes p =
    yes ([↑]ₜ B₁ u′ u″ D₁
                  d′ d″ whnfB₁ whnfu′ whnfu″ p)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂)
                             (D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x) (PE.sym B₂≡B₁) d′
                              , whnfu′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x)
                                         (PE.sym B₂≡B₁)
                                         d″
                               , whnfu″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })

  decConv↑Term′ : ∀ {t u A}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ t [conv↑] t ∷ A → Δ ⊢ u [conv↑] u ∷ A
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term′ Γ≡Δ t u = decConv↑Term t (stabilityConv↑Term (symConEq Γ≡Δ) u)

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A}
               → Γ ⊢ t [conv↓] t ∷ A
               → Γ ⊢ u [conv↓] u ∷ A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  -- True cases
  decConv↓Term (zero-refl x) (zero-refl x₁) = yes (zero-refl x)
  decConv↓Term (Unit-ins t~t) uConv = decConv↓Term-Unit (Unit-ins t~t) uConv
  decConv↓Term (η-unit [t] _ tUnit _) uConv =
    decConv↓Term-Unit (η-unit [t] [t] tUnit tUnit) uConv

  -- Inspective cases
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) with dec~↓ x x₁
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
    in  yes (ℕ-ins k~l′)
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (ℕ , decConv↓Term-ℕ-ins x₂ x))
  decConv↓Term (Empty-ins x) (Empty-ins x₁) with dec~↓ x x₁
  decConv↓Term (Empty-ins x) (Empty-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x)
        ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
        A≡Empty = Empty≡A ⊢Empty≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
    in  yes (Empty-ins k~l′)
  decConv↓Term (Empty-ins x) (Empty-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (Empty , decConv↓Term-Empty-ins x₂ x))
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇)
               with dec~↓ x₃ x₇
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | yes (A , k~l) =
    yes (ne-ins x₁ x₄ x₆ k~l)
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | no ¬p =
    no (λ x₈ → ¬p (decConv↓Term-ne-ins x₆ x₈))
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅)
               with decConv↓  x₂ x₅
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅) | yes p =
    yes (univ x₁ x₃ p)
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅) | no ¬p =
    no (λ { (ne-ins x₆ x₇ () x₉)
          ; (univ x₆ x₇ x₈) → ¬p x₈ })
  decConv↓Term (suc-cong x) (suc-cong x₁) with decConv↑Term  x x₁
  decConv↓Term (suc-cong x) (suc-cong x₁) | yes p =
    yes (suc-cong p)
  decConv↓Term (suc-cong x) (suc-cong x₁) | no ¬p =
    no (λ { (ℕ-ins ([~] A D whnfB ()))
          ; (ne-ins x₂ x₃ () x₅)
          ; (suc-cong x₂) → ¬p x₂ })
  decConv↓Term (Σ-η ⊢t _ tProd _ fstConvT sndConvT)
               (Σ-η ⊢u _ uProd _ fstConvU sndConvU)
    with decConv↑Term fstConvT fstConvU
  ... | yes P with(let ⊢F , ⊢G = syntacticΣ (syntacticTerm ⊢t)
                       fstt≡fstu = soundnessConv↑Term P
                       Gfstt≡Gfstu = substTypeEq (refl ⊢G) fstt≡fstu
                   in  decConv↑TermConv Gfstt≡Gfstu sndConvT sndConvU)
  ... | yes Q = yes (Σ-η ⊢t ⊢u tProd uProd P Q)
  ... | no ¬Q = no (λ { (Σ-η _ _ _ _ _ Q) → ¬Q Q } )
  decConv↓Term (Σ-η _ _ _ _ _ _) (Σ-η _ _ _ _ _ _)
    | no ¬P = no (λ { (Σ-η _ _ _ _ P _) → ¬P P } )
  decConv↓Term (∪₁-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injlₙ injlₙ cnv) (∪₁-η {p₁} {.p₁} {pa₁} {.pa₁} ⊢u ⊢v injlₙ injlₙ cnv′)
    with decConv↑Term cnv cnv′
  ... | yes P = yes (∪₁-η ⊢t ⊢u injlₙ injlₙ P)
  ... | no P = no (λ { (∪₁-η x x₁ injlₙ injlₙ x₄) → P x₄ })
  decConv↓Term (∪₂-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injrₙ injrₙ cnv) (∪₂-η {p₁} {.p₁} {pa₁} {.pa₁} ⊢u ⊢v injrₙ injrₙ cnv′)
    with decConv↑Term cnv cnv′
  ... | yes P = yes (∪₂-η ⊢t ⊢u injrₙ injrₙ P)
  ... | no P = no (λ { (∪₂-η x x₁ injrₙ injrₙ x₄) → P x₄ })
  decConv↓Term (∪₁-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injlₙ injlₙ cnv) (∪₂-η {p₁} {.p₁} {pa₁} {.pa₁} ⊢u ⊢v injrₙ injrₙ cnv′) =
    no c
    where
    c : ∀ {Γ} → ¬ Γ ⊢ injl pa [conv↓] injr pa₁ ∷ A ∪ B
    c (ne-ins x x₁ () x₃)
    c (∪₁-η x x₁ x₂ () x₄)
    c (∪₂-η x x₁ () x₃ x₄)
  decConv↓Term (∪₂-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injrₙ injrₙ cnv) (∪₁-η {p₁} {.p₁} {pa₁} {.pa₁} ⊢u ⊢v injlₙ injlₙ cnv′) =
    no c
    where
    c : ∀ {Γ} → ¬ Γ ⊢ injr pa [conv↓] injl pa₁ ∷ A ∪ B
    c (ne-ins x x₁ () x₃)
    c (∪₁-η x x₁ () x₂ x₄)
    c (∪₂-η x x₁ x₃ () x₄)
  decConv↓Term {Γ = Γ} (∪₁-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injlₙ injlₙ cnv) (∪₃-η {p₁} {.p₁} ⊢A ⊢B ⊢q) =
    no (λ x → decConv↓Term-∪ᵣ x ⊢q q)
    where
    q : ∀ E F → ¬ (Γ ⊢ injl pa ~ p₁ ↓ E ∪ F)
    q E F ([~] A D whnfB ())
  decConv↓Term {Γ = Γ} (∪₂-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injrₙ injrₙ cnv) (∪₃-η {p₁} {.p₁} ⊢A ⊢B ⊢q) =
    no (λ x → decConv↓Term-∪ᵣ x ⊢q q)
    where
    q : ∀ E F → ¬ (Γ ⊢ injr pa ~ p₁ ↓ E ∪ F)
    q E F ([~] A D whnfB ())
  decConv↓Term {Γ = Γ} (∪₃-η {p₁} {.p₁} ⊢A ⊢B ⊢q) (∪₁-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injlₙ injlₙ cnv) =
    no (λ x → decConv↓Term-∪ₗ x ⊢q q)
    where
    q : ∀ E F → ¬ (Γ ⊢ p₁ ~ injl pa ↓ E ∪ F)
    q E F ([~] A D whnfB ())
  decConv↓Term {Γ = Γ} (∪₃-η {p₁} {.p₁} ⊢A ⊢B ⊢q) (∪₂-η {p} {.p} {pa} {.pa} {A} {B} ⊢t ⊢p injrₙ injrₙ cnv) =
    no (λ x → decConv↓Term-∪ₗ x ⊢q q)
    where
    q : ∀ E F → ¬ (Γ ⊢ p₁ ~ injr pa ↓ E ∪ F)
    q E F ([~] A D whnfB ())
  decConv↓Term {Γ = Γ} (∪₃-η {p} {.p} ⊢A ⊢B ⊢p) (∪₃-η {p₁} {.p₁} {A = A₁} {B = B₁} {C = C₁} {D = D₁} ⊢A′ ⊢B′ ⊢p′)
    with dec~↓ ⊢p ⊢p′
  ... | yes (A , k~l) =
    let k≡l₁ = soundness~↓ k~l
        k≡l₂ = soundness~↓ ⊢p
        ⊢A₁ , ⊢t₁ , ⊢t₂ = syntacticEqTerm k≡l₁
        ⊢A₂ , ⊢u₁ , ⊢u₂ = syntacticEqTerm k≡l₂
        w , n₁ , n₂ = ne~↓ k~l
        ⊢≡ = neTypeEq n₁ ⊢t₁ ⊢u₁
        X , Y , xy = ∪≡A (sym ⊢≡) w
        X≡ , Y≡ = ∪-injectivity (PE.subst (λ x → _ ⊢ x ≡ _) xy ⊢≡)
    in  yes (∪₃-η (trans X≡ ⊢A) (trans Y≡ ⊢B) (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) xy k~l))
  ... | no r = no c
    where
    c : ¬ Γ ⊢ p [conv↓] p₁ ∷ C₁ ∪ D₁
    c (∪₁-η x x₁ x₂ x₃ x₄) = InjectionL-Neutral x₂ (proj₁ (proj₂ (ne~↓ ⊢p))) PE.refl
    c (∪₂-η x x₁ x₂ x₃ x₄) = InjectionR-Neutral x₂ (proj₁ (proj₂ (ne~↓ ⊢p))) PE.refl
    c (∪₃-η x x₁ x₂) = r (_ , x₂)
  decConv↓Term (η-eq x₁ x₂ x₃ x₄ x₅) (η-eq x₇ x₈ x₉ x₁₀ x₁₁)
               with decConv↑Term x₅ x₁₁
  decConv↓Term (η-eq x₁ x₂ x₃ x₄ x₅) (η-eq x₇ x₈ x₉ x₁₀ x₁₁) | yes p =
    yes (η-eq x₂ x₇ x₄ x₁₀ p)
  decConv↓Term (η-eq x₁ x₂ x₃ x₄ x₅) (η-eq x₇ x₈ x₉ x₁₀ x₁₁) | no ¬p =
    no (λ { (ne-ins x₁₂ x₁₃ () x₁₅)
          ; (η-eq x₁₃ x₁₄ x₁₅ x₁₆ x₁₇) → ¬p x₁₇ })

  -- False cases
  decConv↓Term  (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (suc-cong x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term  (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (suc-cong x) (zero-refl x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] t ∷ A
                → Γ ⊢ u [conv↑] u ∷ B
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv A≡B t u =
    decConv↑Term t (convConvTerm u (sym A≡B))
