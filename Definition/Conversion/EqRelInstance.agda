{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.Conversion.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening using (_∷_⊆_; wkEq)
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

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function


-- Algorithmic equality of neutrals with injected conversion.
record _⊢_~_∷_ (Γ : Con Term) (k l A : Term) : Set where
  inductive
  constructor ↑
  field
    {B} : Term
    A≡B : Γ ⊢ A ≡ B
    k~↑l : Γ ⊢ k ~ l ↑ B

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A Γ} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl x PE.refl)

~-app : ∀ {f g a b F G Γ}
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
                       B≡ΠHE ([~] _ (red D) whnfB′ x))
             (convConvTerm x₁ F≡H))

~-natrec : ∀ {z z′ s s′ n n′ F F′ Γ}
         → (Γ ∙ ℕ) ⊢ F [conv↑] F′ →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]) →
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ▹ (F ▹▹ F [ suc (var 0) ]↑)) →
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

~-Emptyrec : ∀ {n n′ F F′ Γ}
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

~-sym : {k l A : Term} {Γ : Con Term} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A
~-sym (↑ A≡B x) =
  let ⊢Γ = wfEq A≡B
      B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
  in  ↑ (trans A≡B A≡B′) l~k

~-trans : {k l m A : Term} {Γ : Con Term}
        → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A
        → Γ ⊢ k ~ m ∷ A
~-trans (↑ x x₁) (↑ x₂ x₃) =
  let ⊢Γ = wfEq x
      k~m , _ = trans~↑ (reflConEq ⊢Γ) x₁ x₃
  in  ↑ x k~m

~-wk : {k l A : Term} {ρ : Wk} {Γ Δ : Con Term} →
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : {k l A B : Term} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : {k l A : Term} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
~-to-conv (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)


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
  ∼-trans = ~-trans;
  ≅-conv = convConvTerm;
  ~-conv = ~-conv
  ≅-wk = wkConv↑;
  ≅ₜ-wk = wkConv↑Term;
  ~-wk = ~-wk;
  ≅-red = reductionConv↑;
  ≅ₜ-red = reductionConv↑Term;
  ≅-Urefl = liftConv ∘ᶠ U-refl;
  ≅-ℕrefl = liftConv ∘ᶠ ℕ-refl;
  ≅ₜ-ℕrefl = λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x));
  ≅-Emptyrefl = liftConv ∘ᶠ Empty-refl;
  ≅ₜ-Emptyrefl = λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x));
  ≅-Unitrefl = liftConv ∘ᶠ Unit-refl;
  ≅ₜ-Unitrefl = λ ⊢Γ → liftConvTerm (univ (Unitⱼ ⊢Γ) (Unitⱼ ⊢Γ) (Unit-refl ⊢Γ));
  ≅ₜ-starrefl = liftConvTerm ∘ᶠ star-refl;
  ≅ₜ-η-unit = λ [e] [e'] → let u , uWhnf , uRed = whNormTerm [e]
                               u' , u'Whnf , u'Red = whNormTerm [e']
                               [u] = ⊢u-redₜ uRed
                               [u'] = ⊢u-redₜ u'Red
                               uUnit = whnfUnitary [u] uWhnf
                               u'Unit = whnfUnitary [u'] u'Whnf
                           in  [↑]ₜ Unit u u'
                               (red (idRed:*: (syntacticTerm [e])))
                               (redₜ uRed)
                               (redₜ u'Red)
                               Unitₙ uWhnf u'Whnf
                               (η-unit [u] [u'] uUnit u'Unit);
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
  ≅-Σ-cong = ?;
  ≅ₜ-Σ-cong = ?;
  ≅ₜ-zerorefl = liftConvTerm ∘ᶠ zero-refl;
  ≅-suc-cong = liftConvTerm ∘ᶠ suc-cong;
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x x₁ x₂ x₃ x₄ x₅);
  ≅-Σ-η = ?;
  ~-var = ~-var;
  ~-app = ~-app;
  ~-natrec = ~-natrec;
  ~-Emptyrec = ~-Emptyrec }
