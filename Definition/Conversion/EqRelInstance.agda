{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.EqRelInstance where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening using (_∷_⊆_; wkEq; ▹▹-cong)
open import Definition.Conversion
open import Definition.Conversion.Reduction
open import Definition.Conversion.Universe
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Lift
open import Definition.Conversion.Conversion
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Transitivity
open import Definition.Conversion.Weakening
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Inversion

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function

private
  variable
    m n : Nat
    Γ : Con Term n
    ρ : Wk m n

-- Algorithmic equality of neutrals with injected conversion.
record _⊢_~_∷_ (Γ : Con Term n) (k l A : Term n) : Set where
  inductive
  constructor ↑
  field
    {B} : Term n
    A≡B : Γ ⊢ A ≡ B
    k~↑l : Γ ⊢ k ~ l ↑ B

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl x PE.refl)

~-app : ∀ {f g a b F G}
      → Γ ⊢ f ~ g ∷ Π F ▹ G
      → Γ ⊢ a [conv↑] b ∷ F
      → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ]
~-app (↑ A≡B x) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΠHE = Π≡A ΠFG≡B′ whnfB′
      F≡H , G≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΠHE ΠFG≡B′)
      _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
  in  ↑ (substTypeEq G≡E (refl ⊢f))
        (app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                            B≡ΠHE
                            ([~] _ (red D) whnfB′ x))
             (convConvTerm x₁ F≡H))

~-fst : ∀ {p r F G}
      → Γ ⊢ p ~ r ∷ Σ F ▹ G
      → Γ ⊢ fst p ~ fst r ∷ F
~-fst (↑ A≡B p~r) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΣFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΣHE = Σ≡A ΣFG≡B′ whnfB′
      F≡H , G≡E = Σ-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΣHE ΣFG≡B′)
      p~r↓ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                      B≡ΣHE
                      ([~] _ (red D) whnfB′ p~r)
  in  ↑ F≡H (fst-cong p~r↓)

~-snd : ∀ {p r F G}
      → Γ ⊢ p ~ r ∷ Σ F ▹ G
      → Γ ⊢ snd p ~ snd r ∷ G [ fst p ]
~-snd (↑ A≡B p~r) =
  let ⊢ΣFG , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΣFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΣHE = Σ≡A ΣFG≡B′ whnfB′
      F≡H , G≡E = Σ-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΣHE ΣFG≡B′)
      p~r↓ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                      B≡ΣHE
                      ([~] _ (red D) whnfB′ p~r)
      ⊢F , ⊢G = syntacticΣ ⊢ΣFG
      _ , ⊢p , _ = syntacticEqTerm (soundness~↑ p~r)
      ⊢fst = fstⱼ ⊢F ⊢G (conv ⊢p (sym A≡B))
  in  ↑ (substTypeEq G≡E (refl ⊢fst)) (snd-cong p~r↓)

~-natrec : ∀ {z z′ s s′ n n′ F F′}
         → (Γ ∙ ℕ) ⊢ F [conv↑] F′ →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]) →
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)) →
      Γ ⊢ n ~ n′ ∷ ℕ →
      Γ ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ (F [ n ])
~-natrec x x₁ x₂ (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ℕ≡B′ = trans A≡B (subset* (red D))
      B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl (substType ⊢F ⊢n))
        (natrec-cong x x₁ x₂ k~l′)

~-Emptyrec : ∀ {n n′ F F′}
         → Γ ⊢ F [conv↑] F′ →
      Γ ⊢ n ~ n′ ∷ Empty →
      Γ ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F
~-Emptyrec x (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      Empty≡B′ = trans A≡B (subset* (red D))
      B≡Empty = Empty≡A Empty≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl ⊢F)
        (Emptyrec-cong x k~l′)

~-sym : ∀ {k l A} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A
~-sym (↑ A≡B x) =
  let ⊢Γ = wfEq A≡B
      B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
  in  ↑ (trans A≡B A≡B′) l~k

~-trans : ∀ {k l m A}
        → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A
        → Γ ⊢ k ~ m ∷ A
~-trans (↑ x x₁) (↑ x₂ x₃) =
  let ⊢Γ = wfEq x
      k~m , _ = trans~↑ x₁ x₃
  in  ↑ x k~m

~-wk : ∀ {k l A} {ρ : Wk m n} {Γ Δ} →
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : ∀ {k l A B} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : ∀ {k l A} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
~-to-conv (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)

~-cases : ∀ {A B C C′ B₁ u u′ v v′ t t′}
        → Γ ⊢ A
        → Γ ⊢ B
        → Γ ⊢ C [conv↑] C′
        → Γ ⊢ u [conv↑] u′ ∷ A ▹▹ C
        → Γ ⊢ v [conv↑] v′ ∷ B ▹▹ C
        → Γ ⊢ A ∪ B ≡ B₁
        → Γ ⊢ t ~ t′ ↑ B₁
        → Γ ⊢ cases C t u v ~ cases C′ t′ u′ v′ ∷ C
~-cases {A = A} {B} {C} {C′} {B₁} {u} {u′} {v} {v′} {t} {t′} ⊢A ⊢B C≡C′ u≡u′ v≡v′ ∪≡ t≡t′ =
  let C≡           = soundnessConv↑ C≡C′
      ⊢C , ⊢C′     = syntacticEq C≡
      ⊢AB , ⊢B₁    = syntacticEq ∪≡
      B₂ , wB , rB = whNorm ⊢B₁
      eB           = subset* (red rB)
      D , E , ≡DE  = ∪≡A (trans ∪≡ eB) wB
      C≡ , D≡      = ∪-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) ≡DE (trans ∪≡ eB))
  in  ↑ (refl ⊢C) (cases-cong C≡C′
                              (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ≡DE ([~] B₁ (red rB) wB t≡t′))
                              (convConvTerm u≡u′ (▹▹-cong ⊢A C≡ (refl ⊢C)))
                              (convConvTerm v≡v′ (▹▹-cong ⊢B D≡ (refl ⊢C))))

~-∥ₑ : ∀ {A B B′ B₁ f f′ a a′}
        → Γ ⊢ A
        → Γ ⊢ B [conv↑] B′
        → Γ ⊢ f [conv↑] f′ ∷ A ▹▹ ∥ B ∥
        → Γ ⊢ ∥ A ∥ ≡ B₁
        → Γ ⊢ a ~ a′ ↑ B₁
        → Γ ⊢ ∥ₑ B a f ~ ∥ₑ B′ a′ f′ ∷ ∥ B ∥
~-∥ₑ {A = A} {B} {B′} {B₁} {f} {f′} {a} {a′} ⊢A B≡B′ f≡f′ ∥≡ a≡a′ =
  let B≡           = soundnessConv↑ B≡B′
      ⊢B , ⊢B′     = syntacticEq B≡
      ⊢∥B∥         = ∥ ⊢B ∥ⱼ
      ⊢∥A∥ , ⊢B₁   = syntacticEq ∥≡
      B₂ , wB , rB = whNorm ⊢B₁
      eB           = subset* (red rB)
      D , ≡C       = ∥≡A (trans ∥≡ eB) wB
      C≡           = ∥-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) ≡C (trans ∥≡ eB))
  in  ↑ (refl ⊢∥B∥)
        (∥ₑ-cong B≡B′
                 (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ≡C ([~] B₁ (red rB) wB a≡a′))
                 (convConvTerm f≡f′ (▹▹-cong ⊢A C≡ (refl ⊢∥B∥))))

-- Algorithmic equality instance of the generic equality relation.
instance eqRelInstance : EqRelSet
eqRelInstance = record {
  _⊢_≅_ = _⊢_[conv↑]_;
  _⊢_≅_∷_ = _⊢_[conv↑]_∷_;
  _⊢_~_∷_ = _⊢_~_∷_;
  ~-to-≅ₜ = ~-to-conv;
  ≅-eq = soundnessConv↑;
  ≅ₜ-eq = soundnessConv↑Term;
  ≅-univ = univConv↑;
  ≅-sym = symConv;
  ≅ₜ-sym = symConvTerm;
  ~-sym = ~-sym;
  ≅-trans = transConv;
  ≅ₜ-trans = transConvTerm;
  ~-trans = ~-trans;
  ≅-conv = convConvTerm;
  ~-conv = ~-conv;
  ≅-wk = wkConv↑;
  ≅ₜ-wk = wkConv↑Term;
  ~-wk = ~-wk;
  ≅-red = λ x x₁ x₂ x₃ x₄ → reductionConv↑ x x₁ x₄;
  ≅ₜ-red = λ x x₁ x₂ x₃ x₄ x₅ x₆ → reductionConv↑Term x x₁ x₂ x₆;
  ≅-Urefl = liftConv ∘ᶠ U-refl;
  ≅-ℕrefl = liftConv ∘ᶠ ℕ-refl;
  ≅ₜ-ℕrefl = λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x));
  ≅-Emptyrefl = liftConv ∘ᶠ Empty-refl;
  ≅ₜ-Emptyrefl = λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x));
  ≅-Unitrefl = liftConv ∘ᶠ Unit-refl;
  ≅ₜ-Unitrefl = λ ⊢Γ → liftConvTerm (univ (Unitⱼ ⊢Γ) (Unitⱼ ⊢Γ) (Unit-refl ⊢Γ));
  ≅ₜ-η-unit = λ [e] [e'] → let u , uWhnf , uRed = whNormTerm [e]
                               u' , u'Whnf , u'Red = whNormTerm [e']
                               [u] = ⊢u-redₜ uRed
                               [u'] = ⊢u-redₜ u'Red
                           in  [↑]ₜ Unit u u'
                               (red (idRed:*: (syntacticTerm [e])))
                               (redₜ uRed)
                               (redₜ u'Red)
                               Unitₙ uWhnf u'Whnf
                               (η-unit [u] [u'] uWhnf u'Whnf);
  ≅-Π-cong = λ x x₁ x₂ → liftConv (Π-cong x x₁ x₂);
  ≅ₜ-Π-cong = λ x x₁ x₂ → let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
                              _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
                              ⊢Γ = wfTerm F∷U
                              F<>H = univConv↑ x₁
                              G<>E = univConv↑ x₂
                              F≡H = soundnessConv↑ F<>H
                              E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
                          in  liftConvTerm (univ (Πⱼ F∷U ▹ G∷U) (Πⱼ H∷U ▹ E∷U′)
                                                (Π-cong x F<>H G<>E));
  ≅-Σ-cong = λ x x₁ x₂ → liftConv (Σ-cong x x₁ x₂);
  ≅ₜ-Σ-cong = λ x x₁ x₂ → let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
                              _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
                              ⊢Γ = wfTerm F∷U
                              F<>H = univConv↑ x₁
                              G<>E = univConv↑ x₂
                              F≡H = soundnessConv↑ F<>H
                              E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
                          in  liftConvTerm (univ (Σⱼ F∷U ▹ G∷U) (Σⱼ H∷U ▹ E∷U′)
                                                (Σ-cong x F<>H G<>E));
  ≅-∪-cong = λ x₁ x₂ → liftConv (∪-cong x₁ x₂);
  ≅ₜ-∪-cong = λ x₁ x₂ → let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
                            _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
                            ⊢Γ = wfTerm F∷U
                            F<>H = univConv↑ x₁
                            G<>E = univConv↑ x₂
                            F≡H = soundnessConv↑ F<>H
                        in  liftConvTerm (univ (F∷U ∪ⱼ G∷U) (H∷U ∪ⱼ E∷U)
                                                (∪-cong F<>H G<>E));
  ≅-injl-cong = λ x₁ x₂ → let y , y₁ , y₂ = syntacticEqTerm (soundnessConv↑Term x₂)
                          in liftConvTerm (∪₁-η (injlⱼ x₁ y₁) (injlⱼ x₁ y₂) injlₙ injlₙ x₂);
  ≅-injr-cong = λ x₁ x₂ → let y , y₁ , y₂ = syntacticEqTerm (soundnessConv↑Term x₂)
                          in liftConvTerm (∪₂-η (injrⱼ x₁ y₁) (injrⱼ x₁ y₂) injrₙ injrₙ x₂);
  ~-cases = λ x₁ x₂ x₃ (↑ z x₄) x₅ x₆ → ~-cases x₁ x₂ x₃ x₅ x₆ z x₄;
  ≅-∥-cong = λ x → liftConv (∥-cong x);
  ≅ₜ-∥-cong = λ x → let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x)
                        ⊢Γ = wfTerm F∷U
                        F<>H = univConv↑ x
                        F≡H = soundnessConv↑ F<>H
                    in  liftConvTerm (univ ∥ F∷U ∥ⱼ ∥ H∷U ∥ⱼ
                                           (∥-cong F<>H));
  ≅-∥ᵢ-cong = λ x₁ x₂ → let y , y₁ , y₂ = syntacticEqTerm (soundnessConv↑Term x₂)
                        in liftConvTerm (∥₁-η (∥ᵢⱼ y₁) (∥ᵢⱼ y₂) ∥ᵢₙ ∥ᵢₙ x₂);
  ~-∥ₑ = λ x₁ x₂ (↑ z x₄) x₅ → ~-∥ₑ x₁ x₂ x₅ z x₄ ;
  ≅ₜ-zerorefl = liftConvTerm ∘ᶠ zero-refl;
  ≅-suc-cong = liftConvTerm ∘ᶠ suc-cong;
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x₁ x₂ x₃ x₄ x₅);
  ≅-Σ-η = λ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ → (liftConvTerm (Σ-η x₂ x₃ x₄ x₅ x₆ x₇));
  ~-var = ~-var;
  ~-app = ~-app;
  ~-fst = λ x x₁ x₂ → ~-fst x₂;
  ~-snd = λ x x₁ x₂ → ~-snd x₂;
  ~-natrec = ~-natrec;
  ~-Emptyrec = ~-Emptyrec }
