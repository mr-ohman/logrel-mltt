{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Decidable where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inequality as IE
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.Inversion

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Nat
    Γ Δ : Con Term ℓ

-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A} → Γ ⊢ var n ~ var m ↑ A → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑-app : ∀ {k k₁ l l₁ F F₁ G G₁ B}
          → Γ ⊢ k ∷ Π F ▹ G
          → Γ ⊢ k₁ ∷ Π F₁ ▹ G₁
          → Γ ⊢ k ~ k₁ ↓ B
          → Dec (Γ ⊢ l [conv↑] l₁ ∷ F)
          → Dec (∃ λ A → Γ ⊢ k ∘ l ~ k₁ ∘ l₁ ↑ A)
dec~↑-app k k₁ k~k₁ (yes p) =
  let whnfA , neK , neL = ne~↓ k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
      H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
      F≡H , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) A≡ΠHE ΠFG₁≡A)
  in  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ΠHE k~k₁)
                              (convConvTerm p F≡H))
dec~↑-app k₂ k₃ k~k₁ (no ¬p) =
  no (λ { (_ , app-cong x x₁) →
      let whnfA , neK , neL = ne~↓ x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
      in  ¬p (convConvTerm x₁ (sym F≡F₂)) })

-- Helper function for decidability for neutrals of natural number type.
decConv↓Term-ℕ-ins : ∀ {t u}
                    → Γ ⊢ t [conv↓] u ∷ ℕ
                    → Γ ⊢ t ~ t ↓ ℕ
                    → Γ ⊢ t ~ u ↓ ℕ
decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
decConv↓Term-ℕ-ins (ne-ins x x₁ (gen .Natkind () _) x₃) t~t
decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB ())
decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB ())

-- Helper function for decidability for neutrals of empty type.
decConv↓Term-Empty-ins : ∀ {t u}
                    → Γ ⊢ t [conv↓] u ∷ Empty
                    → Γ ⊢ t ~ t ↓ Empty
                    → Γ ⊢ t ~ u ↓ Empty
decConv↓Term-Empty-ins (Empty-ins x) t~t = x
decConv↓Term-Empty-ins (ne-ins x x₁ (gen .Emptykind () _) x₃) t~t

-- Helper function for decidability for neutrals of a neutral type.
decConv↓Term-ne-ins : ∀ {t u A}
                    → Neutral A
                    → Γ ⊢ t [conv↓] u ∷ A
                    → ∃ λ B → Γ ⊢ t ~ u ↓ B
decConv↓Term-ne-ins (gen .Natkind () _) (ℕ-ins x)
decConv↓Term-ne-ins (gen .Emptykind () _) (Empty-ins x)
decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ x₃) = _ , x₃
decConv↓Term-ne-ins (gen .Ukind () _) (univ x x₁ x₂)
decConv↓Term-ne-ins (gen .Natkind () _) (zero-refl x)
decConv↓Term-ne-ins (gen .Natkind () _) (suc-cong x)
decConv↓Term-ne-ins (gen .Pikind () _) (η-eq x₁ x₂ x₃ x₄ x₅)
decConv↓Term-ne-ins (gen .Unitkind () _) (Unit-ins x)
decConv↓Term-ne-ins (gen .Sigmakind () _) (Σ-η x x₁ x₂ x₃ x₄ x₅)
decConv↓Term-ne-ins (gen .Unitkind () _) (η-unit x x₁ x₂ x₃)

-- Helper function for decidability for impossibility of terms not being equal
-- as neutrals when they are equal as terms and the first is a neutral.
decConv↓Term-ℕ : ∀ {t u}
                → Γ ⊢ t [conv↓] u ∷ ℕ
                → Γ ⊢ t ~ t ↓ ℕ
                → ¬ (Γ ⊢ t ~ u ↓ ℕ)
                → ⊥
decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
decConv↓Term-ℕ (ne-ins x x₁ (gen .Natkind () _) x₃) t~t ¬u~u
decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB ()) ¬u~u
decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB ()) ¬u~u

-- Helper function for extensional equality of Unit.
decConv↓Term-Unit : ∀ {t u}
              → Γ ⊢ t [conv↓] t ∷ Unit → Γ ⊢ u [conv↓] u ∷ Unit
              → Dec (Γ ⊢ t [conv↓] u ∷ Unit)
decConv↓Term-Unit tConv uConv =
  let t≡t = soundnessConv↓Term tConv
      u≡u = soundnessConv↓Term uConv
      _ , [t] , _ = syntacticEqTerm t≡t
      _ , [u] , _ = syntacticEqTerm u≡u
      _ , tWhnf , _ = whnfConv↓Term tConv
      _ , uWhnf , _ = whnfConv↓Term uConv
  in  yes (η-unit [t] [u] tWhnf uWhnf)

mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑ : ∀ {k l R T}
        → Γ ⊢ k ~ k ↑ R → Γ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var-refl {n} x₂ x≡y) (var-refl {m} x₃ x≡y₁) = dec~↑-var-helper x₂ (n ≟ⱽ m)
    where dec~↑-var-helper : ∀ {n m R}
                           → Γ ⊢ var n ∷ R
                           → Dec (n PE.≡ m)
                           → Dec (∃ λ A → Γ ⊢ var n ~ var m ↑ A)
          dec~↑-var-helper x₂ (yes PE.refl) = yes (_ , var-refl x₂ PE.refl)
          dec~↑-var-helper x₂ (no ¬p) = no (λ { (A , k~l) → ¬p (strongVarEq k~l) })

  dec~↑ (app-cong x x₁) (app-cong x₂ x₃) = dec~↑-app-helper x x₁ x₂ x₃ (dec~↓ x x₂)
    where dec~↑-app-helper : ∀ {k k₁ t t₁ F F₁ G G₁}
                           → Γ ⊢ k ~ k ↓ Π F ▹ G
                           → Γ ⊢ t [conv↑] t ∷ F
                           → Γ ⊢ k₁ ~ k₁ ↓ Π F₁ ▹ G₁
                           → Γ ⊢ t₁ [conv↑] t₁ ∷ F₁
                           → Dec (∃ λ A → Γ ⊢ k ~ k₁ ↓ A)
                           → Dec (∃ λ A → Γ ⊢ k ∘ t ~ k₁ ∘ t₁ ↑ A)
          dec~↑-app-helper x x₁ x₂ x₃ (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓ x)
                _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓ x₂)
                ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
                ΠF′G′≡A = neTypeEq neL ⊢l₂ ⊢l
                F≡F′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
            in  dec~↑-app ⊢l₁ ⊢l₂ k~l (decConv↑TermConv F≡F′ x₁ x₃)
          dec~↑-app-helper x x₁ x₂ x₃ (no ¬p) = no (λ { (_ , app-cong x₄ x₅) → ¬p (_ , x₄) })

  dec~↑ (fst-cong {k} k~k) (fst-cong {l} l~l) = dec~↑-fst-helper k~k (dec~↓ k~k l~l)
    where dec~↑-fst-helper : ∀ {k l R G}
                           → Γ ⊢ k ~ k ↓ Σ R ▹ G
                           → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
                           → Dec (∃ λ A → Γ ⊢ fst k ~ fst l ↑ A)
          dec~↑-fst-helper k~k (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
                ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
                F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
            in  yes (F , fst-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                                  A≡ΣFG
                                  k~l))
          dec~↑-fst-helper k~k (no ¬p) = no (λ { (_ , fst-cong x₂) → ¬p (_ , x₂) })

  dec~↑ (snd-cong {k} k~k) (snd-cong {l} l~l) = dec~↑-snd-heler {k = k} k~k (dec~↓ k~k l~l)
    where dec~↑-snd-heler : ∀ {k l F G}
                          → Γ ⊢ k ~ k ↓ Σ F ▹ G
                          → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
                          → Dec (∃ λ A → Γ ⊢ snd k ~ snd l ↑ A)
          dec~↑-snd-heler {k = k} k~k (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
                ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
                F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
            in  yes (G [ fst k ] , snd-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                                            A≡ΣFG
                                            k~l))
          dec~↑-snd-heler k~k (no ¬p) = no (λ { (_ , snd-cong x₂) → ¬p (_ , x₂) })

  dec~↑ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) =
    dec~↑-natrec-helper x₁ x₂ x₃ x₅ x₆ x₇ (decConv↑ x x₄)
    where dec~↑-natrec-helper : ∀ {a₀ a₁ h h₁ k k₁ F F₁}
                              → Γ ⊢ a₀ [conv↑] a₀ ∷ F [ zero ]
                              → Γ ⊢ h [conv↑] h ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                              → Γ ⊢ k ~ k ↓ ℕ
                              → Γ ⊢ a₁ [conv↑] a₁ ∷ F₁ [ zero ]
                              → Γ ⊢ h₁ [conv↑] h₁ ∷ Π ℕ ▹ (F₁ ▹▹ F₁ [ suc (var x0) ]↑)
                              → Γ ⊢ k₁ ~ k₁ ↓ ℕ
                              → Dec (Γ ∙ ℕ ⊢ F [conv↑] F₁)
                              → Dec (∃ λ A → Γ ⊢ natrec F a₀ h k ~ natrec F₁ a₁ h₁ k₁ ↑ A)
          dec~↑-natrec-helper x₁ x₂ x₃ x₅ x₆ x₇ (yes p) =
            dec~↑-natrec-helper′ x₃ p
                                 (decConv↑TermConv (substTypeEq (soundnessConv↑ p)
                                                   (refl (zeroⱼ (wfEqTerm (soundness~↓ x₃)))))
                                                   x₁ x₅)
                                 (decConv↑TermConv (sucCong (soundnessConv↑ p)) x₂ x₆)
                                 (dec~↓ x₃ x₇)
            where dec~↑-natrec-helper′ : ∀ {a₀ a₁ k k₁ h h₁ F F₁}
                                       → Γ ⊢ k ~ k ↓ ℕ
                                       → Γ ∙ ℕ ⊢ F [conv↑] F₁
                                       → Dec (Γ ⊢ a₀ [conv↑] a₁ ∷ F [ zero ])
                                       → Dec (Γ ⊢ h [conv↑] h₁ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑))
                                       → Dec (∃ λ A → Γ ⊢ k ~ k₁ ↓ A)
                                       → Dec (∃ λ A → Γ ⊢ natrec F a₀ h k ~ natrec F₁ a₁ h₁ k₁ ↑ A)
                  dec~↑-natrec-helper′ x₃ p (yes p₁) (yes p₂) (yes (A , k~l)) =
                    let whnfA , neK , neL = ne~↓ k~l
                        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x₃)
                        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
                        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
                        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
                    in  yes (_ , natrec-cong p p₁ p₂ k~l′)
                  dec~↑-natrec-helper′ x₃ p (yes p₁) (yes p₂) (no ¬p) =
                    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p (_ , x₁₁) })
                  dec~↑-natrec-helper′ x₃ p (yes p₁) (no ¬p) r =
                    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₁₀ })
                  dec~↑-natrec-helper′ x₃ p (no ¬p) w r =
                    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₉ })
          dec~↑-natrec-helper x₁ x₂ x₃ x₅ x₆ x₇ (no ¬p) =
            no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₈ })


  dec~↑ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅) =
    dec~↑-Empty-helper x₁ (decConv↑ x x₄) (dec~↓ x₁ x₅)
    where dec~↑-Empty-helper : ∀ {k k₁ R T}
                             → Γ ⊢ k ~ k ↓ Empty
                             → Dec (Γ ⊢ R [conv↑] T)
                             → Dec (∃ λ A → Γ ⊢ k ~ k₁ ↓ A)
                             → Dec (∃ λ A → Γ ⊢ Emptyrec R k ~ Emptyrec T k₁ ↑ A)
          dec~↑-Empty-helper x₁ (yes p) (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x₁)
                ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
                A≡Empty = Empty≡A ⊢Empty≡A whnfA
                k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
            in  yes (_ , Emptyrec-cong p k~l′)
          dec~↑-Empty-helper x₁ (yes p) (no ¬p) = no (λ { (_ , Emptyrec-cong a b) → ¬p (_ , b) })
          dec~↑-Empty-helper x₁ (no ¬p) r = no (λ { (_ , Emptyrec-cong a b) → ¬p a })

  dec~↑ (var-refl x₁ x≡y) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑ (app-cong x₁ x₂) (var-refl x₃ x≡y) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (snd-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (fst-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _) (Emptyrec-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })

  dec~↑′ : ∀ {k l R T}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑ R → Δ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑′ Γ≡Δ k~k l~l = dec~↑ k~k (stability~↑ (symConEq Γ≡Δ) l~l)

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓ : ∀ {k l R T}
        → Γ ⊢ k ~ k ↓ R → Γ ⊢ l ~ l ↓ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        with dec~↑ k~l k~l₁
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
  decConv↓ (ne x) (ne x₁) = decConv↓-ne-helper x (dec~↓ x x₁)
    where decConv↓-ne-helper : ∀ {A B}
                             → Γ ⊢ A ~ A ↓ U
                             → Dec (∃ λ X → Γ ⊢ A ~ B ↓ X)
                             → Dec (Γ ⊢ A [conv↓] B)
          decConv↓-ne-helper x (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , _ = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢k∷U , _ = syntacticEqTerm (soundness~↓ x)
                ⊢U≡A = neTypeEq neK ⊢k∷U ⊢k
                A≡U = U≡A ⊢U≡A
                k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡U k~l
            in  yes (ne k~l′)
          decConv↓-ne-helper x (no ¬p) =
            no (λ x₂ → ¬p (U , decConv↓-ne x₂ x))

  decConv↓ (Π-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) =
    decConv↓-Π-helper x x₂ x₅ (decConv↑ x₁ x₄)
    where decConv↓-Π-helper : ∀ {F F₁ G G₁}
                            → Γ ⊢ F
                            → Γ ∙ F ⊢ G [conv↑] G
                            → Γ ∙ F₁ ⊢ G₁ [conv↑] G₁
                            → Dec (Γ ⊢ F [conv↑] F₁)
                            → Dec (Γ ⊢ Π F ▹ G [conv↓] Π F₁ ▹ G₁)
          decConv↓-Π-helper x x₂ x₅ (yes p) =
            decConv↓-Π-helper′ x p (decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅)
            where decConv↓-Π-helper′ : ∀ {F F₁ G G₁}
                                     → Γ ⊢ F
                                     → Γ ⊢ F [conv↑] F₁
                                     → Dec (Γ ∙ F ⊢ G [conv↑] G₁)
                                     → Dec (Γ ⊢ Π F ▹ G [conv↓] Π F₁ ▹ G₁)
                  decConv↓-Π-helper′ x p (yes p₁) = yes (Π-cong x p p₁)
                  decConv↓-Π-helper′ x p (no ¬p) =
                    no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈) → ¬p x₈ })
          decConv↓-Π-helper x x₂ x₅ (no ¬p) =
            no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈) → ¬p x₇ })

  decConv↓ (Σ-cong x x₁ x₂) (Σ-cong x₃ x₄ x₅) = decConv↓-Σ-helper x x₂ x₅ (decConv↑ x₁ x₄)
    where decConv↓-Σ-helper : ∀ {F F₁ G G₁}
                            → Γ ⊢ F
                            → Γ ∙ F ⊢ G [conv↑] G
                            → Γ ∙ F₁ ⊢ G₁ [conv↑] G₁
                            → Dec (Γ ⊢ F [conv↑] F₁)
                            → Dec (Γ ⊢ Σ F ▹ G [conv↓] Σ F₁ ▹ G₁)
          decConv↓-Σ-helper x x₂ x₅ (yes p) =
            decConv↓-Σ-helper′ x p (decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅)
            where decConv↓-Σ-helper′ : ∀ {F F₁ G G₁}
                                     → Γ ⊢ F
                                     → Γ ⊢ F [conv↑] F₁
                                     → Dec (Γ ∙ F ⊢ G [conv↑] G₁)
                                     → Dec (Γ ⊢ Σ F ▹ G [conv↓] Σ F₁ ▹ G₁)
                  decConv↓-Σ-helper′ x p (yes p₁) = yes (Σ-cong x p p₁)
                  decConv↓-Σ-helper′ x p (no ¬p) =
                    no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈) → ¬p x₈ })
          decConv↓-Σ-helper x x₂ x₅ (no ¬p) =
            no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈) → ¬p x₇ })

  -- False cases
  decConv↓ (U-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.U≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (U-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.ℕ≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (ℕ-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Empty≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Empty-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Unit≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Unit-refl x) (Π-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Σ-cong x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
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
  decConv↓ (Π-cong x x₁ x₂) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (Σ-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Π≢ne neK (soundnessConv↓ x₄)))
  decConv↓ (Σ-cong x x₁ x₂) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (Π-cong x₃ x₄ x₅) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Σ≢ne neK (soundnessConv↓ x₄)))

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
               → Γ ⊢ t [conv↑] t ∷ A → Γ ⊢ u [conv↑] u ∷ A
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
               → Γ ⊢ t [conv↓] t ∷ A → Γ ⊢ u [conv↓] u ∷ A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  -- True cases
  decConv↓Term (zero-refl x) (zero-refl x₁) = yes (zero-refl x)
  decConv↓Term (Unit-ins t~t) uConv = decConv↓Term-Unit (Unit-ins t~t) uConv
  decConv↓Term (η-unit [t] _ tUnit _) uConv =
    decConv↓Term-Unit (η-unit [t] [t] tUnit tUnit) uConv

  -- Inspective cases
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) = decConv↓Term-ℕ-helper x (dec~↓ x x₁)
    where decConv↓Term-ℕ-helper : ∀ {t u}
                                → Γ ⊢ t ~ t ↓ ℕ
                                → Dec (∃ λ A → Γ ⊢ t ~ u ↓ A)
                                → Dec (Γ ⊢ t [conv↓] u ∷ ℕ)
          decConv↓Term-ℕ-helper x (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x)
                ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
                A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
                k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
            in  yes (ℕ-ins k~l′)
          decConv↓Term-ℕ-helper x (no ¬p) =
            no (λ x₂ → ¬p (ℕ , decConv↓Term-ℕ-ins x₂ x))

  decConv↓Term (Empty-ins x) (Empty-ins x₁) =
    decConv↓Term-Empty-helper x (dec~↓ x x₁)
    where decConv↓Term-Empty-helper : ∀ {t u}
            → Γ ⊢ t ~ t ↓ Empty
            → Dec (∃ λ A → Γ ⊢ t ~ u ↓ A)
            → Dec (Γ ⊢ t [conv↓] u ∷ Empty)
          decConv↓Term-Empty-helper x (yes (A , k~l)) =
            let whnfA , neK , neL = ne~↓ k~l
                ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
                _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x)
                ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
                A≡Empty = Empty≡A ⊢Empty≡A whnfA
                k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
            in  yes (Empty-ins k~l′)
          decConv↓Term-Empty-helper x (no ¬p) =
            no (λ x₂ → ¬p (Empty , decConv↓Term-Empty-ins x₂ x))

  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) =
    decConv↓Term-ne-helper x₁ x₄ x₆ (dec~↓ x₃ x₇)
    where decConv↓Term-ne-helper : ∀ {t u A}
            → Γ ⊢ t ∷ A
            → Γ ⊢ u ∷ A
            → Neutral A
            → Dec (∃ λ B → Γ ⊢ t ~ u ↓ B)
            → Dec (Γ ⊢ t [conv↓] u ∷ A)
          decConv↓Term-ne-helper x₁ x₄ x₆ (yes (A , k~l)) =
            yes (ne-ins x₁ x₄ x₆ k~l)
          decConv↓Term-ne-helper x₁ x₄ x₆ (no ¬p) =
            no (λ x₈ → ¬p (decConv↓Term-ne-ins x₆ x₈))

  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅) =
    decConv↓Term-univ-helper x₁ x₃ (decConv↓ x₂ x₅)
    where decConv↓Term-univ-helper : ∀ {t u}
                           → Γ ⊢ t ∷ U
                           → Γ ⊢ u ∷ U
                           → Dec (Γ ⊢ t [conv↓] u)
                           → Dec (Γ ⊢ t [conv↓] u ∷ U)
          decConv↓Term-univ-helper x₁ x₃ (yes p) = yes (univ x₁ x₃ p)
          decConv↓Term-univ-helper x₁ x₃ (no ¬p) =
            no (λ { (ne-ins x₆ x₇ (gen .Ukind () _) x₉)
                  ; (univ x₆ x₇ x₈) → ¬p x₈ })

  decConv↓Term (suc-cong x) (suc-cong x₁) =
    decConv↓Term-suc-helper (decConv↑Term x x₁)
    where decConv↓Term-suc-helper : ∀ {m m₁}
                          → Dec (Γ ⊢ m [conv↑] m₁ ∷ ℕ)
                          → Dec (Γ ⊢ suc m [conv↓] suc m₁ ∷ ℕ)
          decConv↓Term-suc-helper (yes p) = yes (suc-cong p)
          decConv↓Term-suc-helper (no ¬p) =
            no (λ { (ℕ-ins ([~] A D whnfB ()))
                  ; (ne-ins x₂ x₃ (gen .Natkind () _) x₅)
                  ; (suc-cong x₂) → ¬p x₂ })

  decConv↓Term (Σ-η ⊢t _ tProd _ fstConvT sndConvT)
               (Σ-η ⊢u _ uProd _ fstConvU sndConvU) =
    decConv↓Term-Ση-helper ⊢t ⊢u tProd uProd sndConvT sndConvU (decConv↑Term fstConvT fstConvU)
    where decConv↓Term-Ση-helper : ∀ {t u F G}
                         → Γ ⊢ t ∷ Σ F ▹ G
                         → Γ ⊢ u ∷ Σ F ▹ G
                         → Product t
                         → Product u
                         → Γ ⊢ snd t [conv↑] snd t ∷ G [ fst t ]
                         → Γ ⊢ snd u [conv↑] snd u ∷ G [ fst u ]
                         → Dec (Γ ⊢ fst t [conv↑] fst u ∷ F)
                         → Dec (Γ ⊢ t [conv↓] u ∷ Σ F ▹ G)
          decConv↓Term-Ση-helper ⊢t ⊢u tProd uProd sndConvT sndConvU (yes P) =
            decConv↓Term-Ση-helper′ ⊢t ⊢u tProd uProd P
                (let ⊢F , ⊢G = syntacticΣ (syntacticTerm ⊢t)
                     fstt≡fstu = soundnessConv↑Term P
                     Gfstt≡Gfstu = substTypeEq (refl ⊢G) fstt≡fstu
                 in  decConv↑TermConv Gfstt≡Gfstu sndConvT sndConvU)
            where decConv↓Term-Ση-helper′ : ∀ {t u F G}
                            (⊢t : Γ ⊢ t ∷ (Σ F ▹ G))
                            (⊢u : Γ ⊢ u ∷ (Σ F ▹ G))
                            (tProd : Product t)
                            (uProd : Product u)
                            (P : Γ ⊢ fst t [conv↑] fst u ∷ F)
                          → Dec (Γ ⊢ snd t [conv↑] snd u ∷ G [ fst t ])
                          → Dec (Γ ⊢ t [conv↓] u ∷ Σ F ▹ G)
                  decConv↓Term-Ση-helper′ ⊢t ⊢u tProd uProd P (yes Q) = yes (Σ-η ⊢t ⊢u tProd uProd P Q)
                  decConv↓Term-Ση-helper′ ⊢t ⊢u tProd uProd P (no ¬Q) =
                    no (λ { (Σ-η _ _ _ _ _ Q) → ¬Q Q
                          ; (ne-ins _ _ (gen .Sigmakind () _) _)} )
          decConv↓Term-Ση-helper ⊢t ⊢u tProd uProd sndConvT sndConvU (no ¬P) =
            no (λ { (Σ-η _ _ _ _ P _) → ¬P P
                  ; (ne-ins _ _ (gen .Sigmakind () _) _) } )

  decConv↓Term (η-eq x₁ x₂ x₃ x₄ x₅) (η-eq x₇ x₈ x₉ x₁₀ x₁₁) =
    decConv↓Term-ηeq-helper x₂ x₇ x₄ x₁₀ (decConv↑Term x₅ x₁₁)
    where decConv↓Term-ηeq-helper : ∀ {t u F G}
                          → Γ ⊢ t ∷ Π F ▹ G
                          → Γ ⊢ u ∷ Π F ▹ G
                          → Function t
                          → Function u
                          → Dec (Γ ∙ F ⊢ wk1 t ∘ var x0 [conv↑] wk1 u ∘ var x0 ∷ G)
                          → Dec (Γ ⊢ t [conv↓] u ∷ Π F ▹ G)
          decConv↓Term-ηeq-helper x₂ x₇ x₄ x₁₀ (yes p) = yes (η-eq x₂ x₇ x₄ x₁₀ p)
          decConv↓Term-ηeq-helper x₂ x₇ x₄ x₁₀ (no ¬p) =
            no (λ { (ne-ins x₁₂ x₁₃ (gen .Pikind () _) x₁₅)
                  ; (η-eq x₁₃ x₁₄ x₁₅ x₁₆ x₁₇) → ¬p x₁₇ })

  -- False cases
  decConv↓Term  (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (suc-cong x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ()))
          ; (ne-ins x₂ x₃ (gen .Natkind () _) x₅) })
  decConv↓Term  (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (suc-cong x) (zero-refl x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ()))
          ; (ne-ins x₂ x₃ (gen .Natkind () _) x₅) })
  decConv↓Term (ℕ-ins x) (ne-ins x₁ x₂ (gen .Natkind () _) x₄)
  decConv↓Term (Empty-ins x) (ne-ins x₁ x₂ (gen .Emptykind () _) x₄)
  decConv↓Term (ne-ins x x₁ (gen .Natkind () _) x₃) (ℕ-ins x₄)
  decConv↓Term (ne-ins x x₁ (gen .Emptykind () _) x₃) (Empty-ins x₄)
  decConv↓Term (ne-ins x x₁ (gen .Unitkind () _) x₃) (Unit-ins x₄)
  decConv↓Term (ne-ins x x₁ (gen .Ukind () _) x₃) (univ x₄ x₅ x₆)
  decConv↓Term (ne-ins x x₁ (gen .Natkind () _) x₃) (zero-refl x₄)
  decConv↓Term (ne-ins x x₁ (gen .Natkind () _) x₃) (suc-cong x₄)
  decConv↓Term (ne-ins x x₁ (gen .Pikind () _) x₃) (η-eq x₄ x₅ x₆ x₇ x₈)
  decConv↓Term (ne-ins x x₁ (gen .Sigmakind () _) x₃) (Σ-η x₄ x₅ x₆ x₇ x₈ x₉)
  decConv↓Term (ne-ins x x₁ (gen .Unitkind () _) x₃) (η-unit x₄ x₅ x₆ x₇)
  decConv↓Term (univ x x₁ x₂) (ne-ins x₃ x₄ (gen .Ukind () _) x₆)
  decConv↓Term (zero-refl x) (ne-ins x₁ x₂ (gen .Natkind () _) x₄)
  decConv↓Term (suc-cong x) (ne-ins x₁ x₂ (gen .Natkind () _) x₄)
  decConv↓Term (η-eq x x₁ x₂ x₃ x₄) (ne-ins x₅ x₆ (gen .Pikind () _) x₈)
  decConv↓Term (Σ-η x x₁ x₂ x₃ x₄ x₅) (ne-ins x₆ x₇ (gen .Sigmakind () _) x₉)

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] t ∷ A
                → Γ ⊢ u [conv↑] u ∷ B
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv A≡B t u =
    decConv↑Term t (convConvTerm u (sym A≡B))
