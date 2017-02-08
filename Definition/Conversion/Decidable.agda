module Definition.Conversion.Decidable where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.RedSteps
open import Definition.Typed.Reduction
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.InitLemma
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Validity
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Soundness
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.SingleSubst
open import Definition.LogicalRelation.Consequences.Injectivity
open import Definition.LogicalRelation.Consequences.InverseUniv
open import Definition.LogicalRelation.Consequences.Reduction
open import Definition.LogicalRelation.Consequences.Equality
open import Definition.LogicalRelation.Consequences.Inequality

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE


lemx : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑ A → n PE.≡ m
lemx (var x) = PE.refl

decNeutral : (t : Term) → Dec (Neutral t)
decNeutral U = no (λ ())
decNeutral (Π t ▹ t₁) = no (λ ())
decNeutral ℕ = no (λ ())
decNeutral (var x) = yes (var x)
decNeutral (lam t) = no (λ ())
decNeutral (t ∘ t₁) with decNeutral t
decNeutral (t ∘ t₁) | yes p = yes (_∘_ p)
decNeutral (t ∘ t₁) | no ¬p = no (λ { (_∘_ x) → ¬p x })
decNeutral zero = no (λ ())
decNeutral (suc t) = no (λ ())
decNeutral (natrec t t₁ t₂ t₃) with decNeutral t₃
decNeutral (natrec t t₁ t₂ t₃) | yes p = yes (natrec p)
decNeutral (natrec t t₁ t₂ t₃) | no ¬p = no (λ { (natrec x) → ¬p x })

decWhnf : (t : Term) → Dec (Whnf t)
decWhnf U = yes U
decWhnf (Π t ▹ t₁) = yes Π
decWhnf ℕ = yes ℕ
decWhnf (var x) = yes (ne (var x))
decWhnf (lam t) = yes lam
decWhnf (t ∘ t₁) with decNeutral (t ∘ t₁)
decWhnf (t ∘ t₁) | yes p = yes (ne p)
decWhnf (t ∘ t₁) | no ¬p = no (λ { (ne x) → ¬p x })
decWhnf zero = yes zero
decWhnf (suc t) = yes suc
decWhnf (natrec t t₁ t₂ t₃) with decNeutral (natrec t t₁ t₂ t₃)
decWhnf (natrec t t₁ t₂ t₃) | yes p = yes (ne p)
decWhnf (natrec t t₁ t₂ t₃) | no ¬p = no (λ { (ne x) → ¬p x })

{-# NON_TERMINATING #-}
mutual
  dec~↑ : ∀ {k l R T Γ}
        → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
        → Neutral k → Neutral l
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var x₁ x₂) (var x₃ x₄) (var m) (var n) with m ≟ n
  dec~↑ {T = T} (var x₁ x₂) (var x₃ x₄) (var n) (var .n) | yes PE.refl =
    yes (T , var (var x₃ x₄))
  dec~↑ (var x₁ x₂) (var x₃ x₄) (var m) (var n) | no ¬p =
    no (λ { (A , x) → ¬p (lemx x) })

  dec~↑ k₁ l (var n) (_∘_ neL) = no (λ { (_ , ()) })
  dec~↑ k₁ l (var n) (natrec neL) = no (λ { (_ , ()) })
  dec~↑ k₂ l (_∘_ neK) (var n) = no (λ { (_ , ()) })

  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) with dec~↓ k₁ l neK neL
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l)
        with decConv↑TermDecConv k₂ l₁
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l)
        | yes (F<>F₁ , a₁<>a) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        ΠFG₁≡A = lemma3 neK k₁ ⊢k
        H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
        F≡H , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) A≡ΠHE ΠFG₁≡A)
    in  yes (E [ _ ] , app (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ΠHE k~l)
                           (convConvTerm a₁<>a F≡H))
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l) | no ¬p =
    no (λ { (_ , app x x₁) →
       let _ , ⊢g₁ , ⊢g = syntacticEqTerm (soundness~↓ x)
           ΠFG₁≡ΠF₂G₂ = lemma3 neK k₁ ⊢g₁
           ΠF₁G≡ΠF₂G₂ = lemma3 neL l ⊢g
           F≡F₂  , G₁≡G₂ = injectivity ΠFG₁≡ΠF₂G₂
           F₁≡F₂ , G≡G₂  = injectivity ΠF₁G≡ΠF₂G₂
           a₁<>a∷F = convConvTerm x₁ (sym F≡F₂)
       in  ¬p (validEq (trans F≡F₂ (sym F₁≡F₂)) , a₁<>a∷F) })
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | no ¬p =
    no (λ { (_ , app k~l x) → ¬p (_ , k~l) })

  dec~↑ k₂ l (_∘_ neK) (natrec neL) = no (λ { (_ , ()) })
  dec~↑ k₂ l (natrec neK) (var n) = no (λ { (_ , ()) })
  dec~↑ k₂ l (natrec neK) (_∘_ neL) = no (λ { (_ , ()) })

  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    with dec~↓ k₃ l₂ neK neL
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) with decConv↑ x x₁
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | yes p
    with decConv↑TermConv k₁ l
           (substTypeEq (soundnessConv↑ p) (refl (zero (wfTerm k₃))))
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | yes p | yes p₁
    with decConv↑TermConv k₂ l₁ (sucCong (soundnessConv↑ p))
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | yes p | yes p₁ | yes p₂ =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        ⊢ℕ≡A = lemma3 neK k₃ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l' = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
    in  yes (_ , natrec p p₁ p₂ k~l')
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | yes p | yes p₁ | no ¬p =
    no (λ { (_ , natrec x₂ x₃ x₄ k~l) → ¬p x₄ })
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | yes p | no ¬p =
    no (λ { (_ , natrec x₂ x₃ x₄ k~l) → ¬p x₃ })
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) | no ¬p = no (λ { (_ , natrec x₂ x₃ x₄ k~l) → ¬p x₂ })
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | no ¬p = no (λ { (_ , natrec x₂ x₃ x₄ k~l) → ¬p (ℕ , k~l) })

  dec~↑ k (conv l x) neK neL = dec~↑ k l neK neL
  dec~↑ (conv k x) l neK neL = dec~↑ k l neK neL


  dec~↓ : ∀ {k l R T Γ}
        → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
        → Neutral k → Neutral l
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ k l neK neL with dec~↑ k l neK neL
  dec~↓ k₁ l₁ neK neL | yes (A , k~l) =
    let ⊢A = proj₁ (syntacticEqTerm (soundness~↑ k~l))
        B , whnfB , D = fullyReducible ⊢A
    in  yes (B , [~] A (red D) whnfB k~l)
  dec~↓ k₁ l₁ neK neL | no ¬p =
    no (λ { (A , [~] B D whnfA k~l) → ¬p (B , k~l) })


  decConv↑' : ∀ {A B Γ Δ l l'}
            → ⊢ Γ ≡ Δ
            → Γ ⊩⟨ l ⟩ A
            → _⊩⟨_⟩_ {{eqRelInstance}} Δ l' B
            → Dec (Γ ⊢ A [conv↑] B)
  decConv↑' Γ≡Δ (U' .⁰ 0<1 ⊢Γ) (U' .⁰ 0<1 ⊢Γ₁) =
    yes ([↑] U U (id (U ⊢Γ)) (id (U ⊢Γ)) U U (U-refl ⊢Γ))
  decConv↑' Γ≡Δ (U _) (ℕ D) =
    no (λ x → U≢ℕ-red (red D) (soundnessConv↑ (stabilityConv↑ Γ≡Δ x)))
  decConv↑' Γ≡Δ (U _) (ne' K D neK K≡K) =
    no (λ x → U≢ne-red (red D) neK (soundnessConv↑ (stabilityConv↑ Γ≡Δ x)))
  decConv↑' Γ≡Δ (U _) (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) =
    no (λ x → U≢Π-red (red D) (soundnessConv↑ (stabilityConv↑ Γ≡Δ x)))
  decConv↑' Γ≡Δ (ℕ D) (U _) =
    no (λ x → U≢ℕ-red (red D) (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (ℕ [ ⊢A , ⊢B , D ]) (ℕ [ ⊢A₁ , ⊢B₁ , D₁ ]) =
    yes ([↑] ℕ ℕ D (stabilityRed* (symConEq Γ≡Δ) D₁) ℕ ℕ (ℕ-refl (wf ⊢A)))
  decConv↑' Γ≡Δ (ℕ D) (ne' K D' neK K≡K) =
    no (λ x → ℕ≢ne-red (red D) (stabilityRed* (symConEq Γ≡Δ) (red D')) neK
                       (soundnessConv↑ x))
  decConv↑' Γ≡Δ (ℕ D) (Π' F G D' ⊢F ⊢G A≡A [F] [G] G-ext) =
    no (λ x → ℕ≢Π-red (red D) (stabilityRed* (symConEq Γ≡Δ) (red D'))
                      (soundnessConv↑ x))
  decConv↑' Γ≡Δ (ne' K D neK K≡K) (U _) =
    no (λ x → U≢ne-red (red D) neK (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (ne' K D neK K≡K) (ℕ D') =
    no (λ x → ℕ≢ne-red (stabilityRed* (symConEq Γ≡Δ) (red D')) (red D) neK
                       (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
            (ne' K₁ [ ⊢A₁ , ⊢B₁ , D₁ ] neK₁ K≡K₁)
            with dec~↓ (inverseUnivNe neK ⊢B)
                       (stabilityTerm (symConEq Γ≡Δ) (inverseUnivNe neK₁ ⊢B₁))
                       neK neK₁
  decConv↑' Γ≡Δ (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
            (ne' K₁ [ ⊢A₁ , ⊢B₁ , D₁ ] neK₁ K≡K₁) | yes (A , k~l) =
    yes ([↑] K K₁ D (stabilityRed* (symConEq Γ≡Δ) D₁) (ne neK) (ne neK₁) (ne {!!}))
  decConv↑' Γ≡Δ (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K))
            (ne (ne K₁ [ ⊢A₁ , ⊢B₁ , D₁ ] neK₁ K≡K₁)) | no ¬p =
    no (λ x → ¬p {!!})
  decConv↑' Γ≡Δ (ne (ne K D neK K≡K)) (Π (Π F G D' ⊢F ⊢G A≡A [F] [G] G-ext)) =
    no (λ x → Π≢ne-red (stabilityRed* (symConEq Γ≡Δ) (red D')) (red D) neK
                       (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (U _) =
    no (λ x → U≢Π-red (red D) (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕ D') =
    no (λ x → ℕ≢Π-red (stabilityRed* (symConEq Γ≡Δ) (red D')) (red D)
                      (sym (soundnessConv↑ x)))
  decConv↑' Γ≡Δ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D' neK K≡K)) =
    no (λ x → Π≢ne-red (red D) (stabilityRed* (symConEq Γ≡Δ) (red D')) neK
                       (soundnessConv↑ x))
  decConv↑' Γ≡Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
            with PE.subst₂ (λ x y → Dec (_ ⊢ x [conv↑] y))
                           (wk-id F zero) (wk-id F₁ zero)
                           (decConv↑' Γ≡Δ ([F] id (wf ⊢F)) ([F]₁ id (wf ⊢F₁)))
  decConv↑' Γ≡Δ (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext))
            (Π (Π F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) | yes p
            with let ⊢Γ∙F    = wf ⊢F ∙ ⊢F
                     ⊢Δ∙F₁   = wf ⊢F₁ ∙ ⊢F₁
                     var0    = var ⊢Γ∙F here
                     var0'   = var ⊢Δ∙F₁ here
                     [var0]  = neuTerm ([F] (step id) ⊢Γ∙F) (var zero)
                                       var0 (refl var0)
                     [var0]' = neuTerm ([F]₁ (step id) ⊢Δ∙F₁) (var zero)
                                       var0' (refl var0')
                     F≡F₁    = soundnessConv↑ p
                 in  PE.subst₂ (λ x y → Dec (_ ⊢ x [conv↑] y))
                               (substVar0Id G) (substVar0Id G₁)
                               (decConv↑' (Γ≡Δ ∙ F≡F₁)
                                          ([G] (step id) ⊢Γ∙F [var0])
                                          ([G]₁ (step id) ⊢Δ∙F₁ [var0]'))
  decConv↑' Γ≡Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
    | yes p | yes p₁ =
    yes ([↑] (Π F ▹ G) (Π F₁ ▹ G₁)
             (red D) (stabilityRed* (symConEq Γ≡Δ) (red D₁))
             Π Π (Π-cong ⊢F p p₁))
  decConv↑' Γ≡Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
    | yes p | no ¬p =
    no (λ x → ¬p
        let ΠFG≡ΠF₁G₁ = reduction' (red D)
                                   (stabilityRed* (symConEq Γ≡Δ) (red D₁))
                                   Π Π (soundnessConv↑ x)
            F≡F₁ , G≡G₁ = injectivity ΠFG≡ΠF₁G₁
        in  validEq G≡G₁)
  decConv↑' Γ≡Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Π' F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) | no ¬p =
    no (λ x → ¬p
        let ΠFG≡ΠF₁G₁ = reduction' (red D)
                                   (stabilityRed* (symConEq Γ≡Δ) (red D₁))
                                   Π Π (soundnessConv↑ x)
            F≡F₁ , G≡G₁ = injectivity ΠFG≡ΠF₁G₁
        in  validEq F≡F₁)
  decConv↑' Γ≡Δ [A] (emb 0<1 [B]) = decConv↑' Γ≡Δ [A] [B]
  decConv↑' Γ≡Δ (emb 0<1 [A]) [B] = decConv↑' Γ≡Δ [A] [B]

  decConv↓' : ∀ {A B Γ Δ l l'}
            → ⊢ Γ ≡ Δ
            → Γ ⊩⟨ l ⟩ A
            → _⊩⟨_⟩_ {{eqRelInstance}} Δ l' B
            → Whnf A → Whnf B
            → Dec (Γ ⊢ A [conv↓] B)
  decConv↓' Γ≡Δ [A] [B] whnfA whnfB with decConv↑' Γ≡Δ [A] [B]
  decConv↓' Γ≡Δ [A] [B] whnfA whnfB
            | yes ([↑] A' B' D D' whnfA' whnfB' A'<>B')
            rewrite whnfRed*' D whnfA | whnfRed*' D' whnfB =
    yes A'<>B'
  decConv↓' Γ≡Δ [A] [B] whnfA whnfB | no ¬p =
    let ⊢A = wellformed [A]
        ⊢B = stability (symConEq Γ≡Δ) (wellformed [B])
    in  no (λ x → ¬p ([↑] _ _ (id ⊢A) (id ⊢B) whnfA whnfB x))

  decConv↑Term' : ∀ {t u A Γ l}
                  ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ∷ A / [A]
                → Γ ⊩⟨ l ⟩ u ∷ A / [A]
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term' (U' .⁰ 0<1 ⊢Γ)
                (Uₜ A d typeA A≡A [t]) (Uₜ A₁ d₁ typeA₁ A≡A₁ [t]₁)
                with decConv↑' (reflConEq ⊢Γ) [t] [t]₁
  decConv↑Term' (U (U .⁰ 0<1 ⊢Γ))
                (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [t])
                (Uₜ A₁ [ ⊢t₁ , ⊢u₁ , d₁ ] typeA₁ A≡A₁ [t]₁)
                | yes ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    yes ([↑]ₜ U A A₁ (id (U ⊢Γ)) d d₁
              U (typeWhnf typeA) (typeWhnf typeA₁)
              (univ ⊢u ⊢u₁ {!A'<>B'!}))
  decConv↑Term' (U (U .⁰ 0<1 ⊢Γ))
                (Uₜ A d typeA A≡A [t]) (Uₜ A₁ d₁ typeA₁ A≡A₁ [t]₁) | no ¬p =
    no (λ x → ¬p {!!})
  decConv↑Term' {l = l} (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ _ d n≡n suc prop) (ℕₜ _ d₁ n≡n₁ suc prop₁)
                with decConv↑Term' {l = l} (ℕ ([ ⊢A , ⊢B , D ])) prop prop₁
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ _ [ ⊢t , ⊢u , d ] n≡n suc prop)
                (ℕₜ _ [ ⊢t₁ , ⊢u₁ , d₁ ] n≡n₁ suc prop₁) | yes p =
    yes ([↑]ₜ ℕ (suc _) (suc _) D d d₁ ℕ suc suc
              (suc-cong (convConvTerm p (subset* D))))
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ _ d n≡n suc prop) (ℕₜ _ d₁ n≡n₁ suc prop₁) | no ¬p =
    no (λ x → ¬p
        let q = reductionₜ' D (redₜ d) (redₜ d₁) ℕ suc suc
                            (soundnessConv↑Term x)
        in  {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ _ d n≡n suc prop) (ℕₜ .zero d₁ n≡n₁ zero prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ _ d n≡n suc prop) (ℕₜ n d₁ n≡n₁ (ne x) prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ .zero d n≡n zero prop) (ℕₜ _ d₁ n≡n₁ suc prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ .zero [ ⊢t , ⊢u , d ] n≡n zero prop)
                (ℕₜ .zero [ ⊢t₁ , ⊢u₁ , d₁ ] n≡n₁ zero prop₁) =
    yes ([↑]ₜ ℕ zero zero D d d₁ ℕ zero zero (zero-refl (wf ⊢A)))
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ .zero d n≡n zero prop) (ℕₜ n d₁ n≡n₁ (ne x) prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ n d n≡n (ne x) prop) (ℕₜ _ d₁ n≡n₁ suc prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ n₁ d n≡n (ne x) prop) (ℕₜ .zero d₁ n≡n₁ zero prop₁) =
    no (λ x → {!!})
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ n [ ⊢t , ⊢u , d ] n≡n (ne x) prop)
                (ℕₜ n₁ [ ⊢t₁ , ⊢u₁ , d₁ ] n≡n₁ (ne x₁) prop₁)
                with dec~↓ ⊢u ⊢u₁ x x₁
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D₁ ])
                (ℕₜ n [ ⊢t , ⊢u , d ] n≡n (ne x) prop)
                (ℕₜ n₁ [ ⊢t₁ , ⊢u₁ , d₁ ] n≡n₁ (ne x₁) prop₁)
                | yes (A , k~l) =
    yes ([↑]ₜ ℕ n n₁ D₁ d d₁ ℕ (ne x) (ne x₁) (ℕ-ins {!!}))
  decConv↑Term' (ℕ [ ⊢A , ⊢B , D ])
                (ℕₜ n₁ [ ⊢t , ⊢u , d ] n≡n (ne x) prop)
                (ℕₜ n [ ⊢t₁ , ⊢u₁ , d₁ ] n≡n₁ (ne x₁) prop₁)
                | no ¬p =
    no (λ x → ¬p {!!})
  decConv↑Term' (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
                (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k))
                (neₜ k₁ [ ⊢t₁ , ⊢u₁ , d₁ ] (neNfₜ neK₂ ⊢k₁ k≡k₁))
                with dec~↓ ⊢u ⊢u₁ neK₁ neK₂
  decConv↑Term' (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
                (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k))
                (neₜ k₁ [ ⊢t₁ , ⊢u₁ , d₁ ] (neNfₜ neK₂ ⊢k₁ k≡k₁))
                | yes (A , k~l) =
    yes ([↑]ₜ K k k₁ D d d₁ (ne neK) (ne neK₁) (ne neK₂) (ne-ins ⊢k ⊢k₁ neK k~l))
  decConv↑Term' (ne' K [ ⊢A , ⊢B , D ] neK K≡K)
                (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k))
                (neₜ k₁ [ ⊢t₁ , ⊢u₁ , d₁ ] (neNfₜ neK₂ ⊢k₁ k≡k₁))
                | no ¬p =
    no (λ x → ¬p {!!})
  decConv↑Term' (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext)
                (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁)
                (f₁ , [ ⊢t₁ , ⊢u₁ , d₁ ] , funcF₁ , f≡f₁ , [f]₂ , [f]₃)
                with let ⊢Γ∙F   = wf ⊢F ∙ ⊢F
                         var0   = var ⊢Γ∙F here
                         [var0] = neuTerm ([F] (step id) ⊢Γ∙F) (var zero)
                                          var0 (refl var0)
                     in  PE.subst (λ x → Dec (_ ⊢ _ [conv↑] _ ∷ x))
                                  (substVar0Id G)
                                  (decConv↑Term' ([G] (step id) ⊢Γ∙F [var0])
                                                 ([f]₁ (step id) ⊢Γ∙F [var0])
                                                 ([f]₃ (step id) ⊢Γ∙F [var0]))
  decConv↑Term' (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext)
                (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁)
                (f₁ , [ ⊢t₁ , ⊢u₁ , d₁ ] , funcF₁ , f≡f₁ , [f]₂ , [f]₃)
                | yes p =
    yes ([↑]ₜ (Π F ▹ G) f f₁ D d d₁ Π (functionWhnf funcF) (functionWhnf funcF₁)
              (fun-ext ⊢F ⊢u ⊢u₁ (functionWhnf funcF) (functionWhnf funcF₁) p))
  decConv↑Term' (Π' F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext)
                (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁)
                (f₁ , [ ⊢t₁ , ⊢u₁ , d₁ ] , funcF₁ , f≡f₁ , [f]₂ , [f]₃)
                | no ¬p =
    no (λ t<>u →
          let ⊢Γ∙F = wf ⊢F ∙ ⊢F
              f≡f₁ = reductionₜ' D d d₁ Π
                                 (functionWhnf funcF) (functionWhnf funcF₁)
                                 (soundnessConv↑Term t<>u)
          in  ¬p (validEqTerm (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                                        (substVar0Id G)
                                        (app-cong (wkEqTerm (step id) ⊢Γ∙F f≡f₁)
                                                  (refl (var ⊢Γ∙F here))))))
  decConv↑Term' (emb 0<1 [A]) [t] [u] =
    decConv↑Term' [A] (irrelevanceTerm (emb 0<1 [A]) [A] [t])
                       (irrelevanceTerm (emb 0<1 [A]) [A] [u])

  decConv↓Term' : ∀ {t u A Γ l}
                  ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ∷ A / [A]
                → Γ ⊩⟨ l ⟩ u ∷ A / [A]
                → Whnf t → Whnf u → Whnf A
                → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv↓Term' [A] [t] [u] whnfT whnfU whnfA with decConv↑Term' [A] [t] [u]
  decConv↓Term' [A] [t] [u] whnfT whnfU whnfA
                | yes ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u)
                rewrite whnfRed*' D whnfA | whnfRed* d whnfT | whnfRed* d' whnfU =
    yes t<>u
  decConv↓Term' [A] [t] [u] whnfT whnfU whnfA | no ¬p =
    let ⊢A = wellformed [A]
        ⊢t = wellformedTerm [A] [t]
        ⊢u = wellformedTerm [A] [u]
    in  no (λ x → ¬p ([↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢u) whnfA whnfT whnfU x))

  decConv↑ : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ A B with fundamental A | fundamental B
  decConv↑ A B | [Γ] , [A] | [Γ]' , [B] =
    let ⊢Γ = wf A
        [σA] = soundness [Γ] [A]
        [σB] = soundness [Γ]' [B]
    in  decConv↑' (reflConEq ⊢Γ) [σA] [σB]

  decConv↓ : ∀ {A B Γ}
           → Γ ⊢ A → Γ ⊢ B
           → Whnf A → Whnf B
           → Dec (Γ ⊢ A [conv↓] B)
  decConv↓ A B whnfA whnfB with fundamental A | fundamental B
  decConv↓ A B whnfA whnfB | [Γ] , [A] | [Γ]' , [B] =
    let ⊢Γ = wf A
        [σA] = soundness [Γ] [A]
        [σB] = soundness [Γ]' [B]
    in  decConv↓' (reflConEq ⊢Γ) [σA] [σB] whnfA whnfB

  decConv↑Term : ∀ {t u A Γ}
               → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term {t} {u} {A} ⊢t ⊢u with fundamentalTerm ⊢t | fundamentalTerm ⊢u
  decConv↑Term {t} {u} {A} ⊢t ⊢u | [Γ] , [A] , [t] | [Γ]' , [A]' , [u] =
    let ⊢Γ = wfTerm ⊢t
        [σA] = soundness [Γ] [A]
        [σA]' = soundness [Γ]' [A]'
        [σt] = soundnessTerm {t} {A} [Γ] [A] [t]
        [σu] = soundnessTerm {u} {A} [Γ]' [A]' [u]
    in  decConv↑Term' [σA] [σt] (irrelevanceTerm [σA]' [σA] [σu])

  decConv↓Term : ∀ {t u A Γ}
               → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A
               → Whnf t → Whnf u → Whnf A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv↓Term {t} {u} {A} ⊢t ⊢u whnfT whnfU whnfA with fundamentalTerm ⊢t | fundamentalTerm ⊢u
  decConv↓Term {t} {u} {A} ⊢t ⊢u whnfT whnfU whnfA | [Γ] , [A] , [t] | [Γ]' , [A]' , [u] =
    let ⊢Γ = wfTerm ⊢t
        [σA] = soundness [Γ] [A]
        [σA]' = soundness [Γ]' [A]'
        [σt] = soundnessTerm {t} {A} [Γ] [A] [t]
        [σu] = soundnessTerm {u} {A} [Γ]' [A]' [u]
    in  decConv↓Term' [σA] [σt] (irrelevanceTerm [σA]' [σA] [σu]) whnfT whnfU whnfA

  decConv↑TermConv : ∀ {t u A B Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B
                → Γ ⊢ A ≡ B → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv t u A≡B = decConv↑Term t (conv u (sym A≡B))

  decConv↑TermDecConv : ∀ {t u A B Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B
           → Dec (Γ ⊢ A [conv↑] B × (Γ ⊢ t [conv↑] u ∷ A))
  decConv↑TermDecConv t u with decConv↑ (syntacticTerm t) (syntacticTerm u)
  decConv↑TermDecConv t u | yes p with decConv↑TermConv t u (soundnessConv↑ p)
  decConv↑TermDecConv t₁ u₁ | yes p | yes p₁ = yes (p , p₁)
  decConv↑TermDecConv t₁ u₁ | yes p | no ¬p = no (λ { (x , y) → ¬p y })
  decConv↑TermDecConv t u | no ¬p = no (λ { (x , y) → ¬p x })
