{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation


module Definition.LogicalRelation.Substitution.Introductions.TruncE {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as Wk hiding (wkTerm; wkEqTerm) renaming (wk to ⊢wk ; wkEq to ⊢wkEq)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Trunc
open import Definition.LogicalRelation.Substitution.Introductions.Cases
  using (▹▹∘ⱼ ; appTermNd ; redSecond*Term ; ⊩ₗ ; ⊩ᵣ ; ≡⊩▹▹ ; ⊩▹▹-cong ; app-congTermNd)
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Application

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    Γ : Con Term n

∥ₑ-subst* : ∀ {A B a a′ f}
             → Γ ⊢ A
             → Γ ⊢ B
             → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
             → Γ ⊢ a ⇒* a′ ∷ ∥ A ∥
             → Γ ⊢ ∥ₑ B a f ⇒* ∥ₑ B a′ f ∷ ∥ B ∥
∥ₑ-subst* ⊢A ⊢B ⊢f (id x) = id (∥ₑⱼ x ⊢f ⊢B)
∥ₑ-subst* ⊢A ⊢B ⊢f (x ⇨ a⇒a′) = ∥ₑ-subst ⊢A ⊢B ⊢f x ⇨ ∥ₑ-subst* ⊢A ⊢B ⊢f a⇒a′

∥ₑ-subst*ᵢ : ∀ {A B a a′ f x}
              → Γ ⊢ A
              → Γ ⊢ B
              → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
              → Γ ⊢ x ∷ A
              → Γ ⊢ a ⇒* a′ ∷ ∥ A ∥
              → TruncI a′ x
              → Γ ⊢ ∥ₑ B a f ⇒* f ∘ x ∷ ∥ B ∥
∥ₑ-subst*ᵢ ⊢A ⊢B ⊢f ⊢x a⇒a′ ∥ᵢₙ =
  ∥ₑ-subst* ⊢A ⊢B ⊢f a⇒a′
  ⇨∷* (∥-β ⊢A ⊢B ⊢x ⊢f
       ⇨ id (▹▹∘ⱼ ⊢f ⊢x))

-- Reducibility of ∥ₑ with a specific typing derivation
∥ₑ′ : ∀ {A B a f l l′}
         ([B] : Γ ⊩⟨ l ⟩ B)
         ([∥A∥] : Γ ⊩⟨ l′ ⟩∥ ∥ A ∥)
         ([∥B∥] : Γ ⊩⟨ l ⟩ ∥ B ∥)
         ([▹▹AB] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ ∥ B ∥)
         ([a] : Γ ⊩⟨ l′ ⟩ a ∷ ∥ A ∥ / ∥-intr [∥A∥])
         ([f] : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB])
       → Γ ⊩⟨ l ⟩ ∥ₑ B a f ∷ ∥ B ∥ / [∥B∥]
∥ₑ′ {Γ = Γ} {A = A} {B = B} {a = a} {f = f} {l} {l′}
       [B]
       (noemb (∥ᵣ A' D ⊢A A≡A [A']))
       [∥B∥]
       [▹▹AB] (∥₁ₜ p d ep pa i x) [f]
  with ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
... | PE.refl =
  proj₁ (redSubst*Term
          (∥ₑ-subst*ᵢ
            ⊢A (escape [B])
            (escapeTerm (▹▹-intr [▹▹AB]) [f])
            (escapeTerm (irrelevance′ (wk-id A) ([A'] id (wf ⊢A))) [pa])
            (redₜ d) i)
          [∥B∥] (appTermNd [A] [∥B∥] (▹▹-intr [▹▹AB]) [f] [pa]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ A / [A]
  [pa] = irrelevanceTerm′ (wk-id A) ([A'] id (wf ⊢A)) [A] x
∥ₑ′ {Γ = Γ} {A = A} {B = B} {a = a} {f = f} {l} {l′}
       [B]
       (noemb (∥ᵣ A' [ ⊢AB , ⊢AB' , D ] ⊢A' A≡A [A']))
       [∥B∥]
       [▹▹AB] (∥₂ₜ p [ ⊢t , ⊢p , d ] ep (neNfₜ neK ⊢k k≡k)) [f] =
  proj₁ (redSubst*Term redc [∥B∥] vc)
  where
  ⊢∥≡ : Γ ⊢ ∥ A ∥ ≡ ∥ A' ∥
  ⊢∥≡ = subset* D

  ∥≡ : ∥ A ∥ PE.≡ ∥ A' ∥
  ∥≡ = whnfRed* D ∥ₙ

  ⊢A : Γ ⊢ A
  ⊢A = PE.subst (λ x → Γ ⊢ x) (PE.sym (∥-PE-injectivity ∥≡)) ⊢A'

  redc : Γ ⊢ ∥ₑ B a f ⇒* ∥ₑ B p f ∷ ∥ B ∥
  redc = ∥ₑ-subst* ⊢A (escape [B]) (escapeTerm (▹▹-intr [▹▹AB]) [f]) (conv* d (sym ⊢∥≡))

  nc : Neutral (∥ₑ B p f)
  nc = ∥ₑₙ neK

  ⊢c : Γ ⊢ ∥ₑ B p f ∷ ∥ B ∥
  ⊢c = redSecond*Term redc

  vc : Γ ⊩⟨ l ⟩ ∥ₑ B p f ∷ ∥ B ∥ / [∥B∥]
  vc = neuTerm [∥B∥] nc ⊢c (~-∥ₑ ⊢A (escape [B]) (escapeEq [B] (reflEq [B]))
                                 (~-conv k≡k (sym ⊢∥≡))
                                 (escapeTermEq (▹▹-intr [▹▹AB]) (reflEqTerm (▹▹-intr [▹▹AB]) [f])))
∥ₑ′ {Γ = Γ} {a = a} {f = f} {l = l} [B] (emb 0<1 (noemb (∥ᵣ S D ⊢S A≡A [S]))) [∥B∥] [▹▹AB] [a] [f] =
  ∥ₑ′ [B] (noemb (∥ᵣ S D ⊢S A≡A [S])) [∥B∥] [▹▹AB] [a] [f]

∥ₑ″ : ∀ {A B a f l l′}
         ([B] : Γ ⊩⟨ l ⟩ B)
         ([∥A∥] : Γ ⊩⟨ l′ ⟩ ∥ A ∥)
         ([∥B∥] : Γ ⊩⟨ l ⟩ ∥ B ∥)
         ([▹▹AB] : Γ ⊩⟨ l ⟩ A ▹▹ ∥ B ∥)
         ([a] : Γ ⊩⟨ l′ ⟩ a ∷ ∥ A ∥ / [∥A∥])
         ([f] : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / [▹▹AB])
       → Γ ⊩⟨ l ⟩ ∥ₑ B a f ∷ ∥ B ∥ / [∥B∥]
∥ₑ″ {Γ = Γ} {A = A} {B = B} {a = a} {f = f} {l} {l′} [B] [∥A∥] [∥B∥] [▹▹AB] [a] [f] =
  ∥ₑ′ [B] (∥-elim [∥A∥]) [∥B∥] (▹▹-elim [▹▹AB])
         (irrelevanceTerm [∥A∥] (∥-intr (∥-elim [∥A∥])) [a])
         (irrelevanceTerm [▹▹AB] (▹▹-intr (▹▹-elim [▹▹AB])) [f])

∥ₑ-cong′ : ∀ {A B B′ a a′ f f′ l l′}
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([B′]   : Γ ⊩⟨ l ⟩ B′)
            ([B≡B′] : Γ ⊩⟨ l ⟩ B ≡ B′ / [B])
            ([∥A∥]  : Γ ⊩⟨ l′ ⟩∥ ∥ A ∥)
            ([∥B∥]  : Γ ⊩⟨ l ⟩ ∥ B ∥)
            ([▹▹AB] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ ∥ B ∥)
            ([a≡a′] : Γ ⊩⟨ l′ ⟩ a ≡ a′ ∷ ∥ A ∥ / ∥-intr [∥A∥])
            ([f≡f′] : Γ ⊩⟨ l ⟩ f ≡ f′ ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB])
            → Γ ⊩⟨ l ⟩ ∥ₑ B a f ≡ ∥ₑ B′ a′ f′ ∷ ∥ B ∥ / [∥B∥]
∥ₑ-cong′ {Γ = Γ} {A = A} {B = B} {B′ = B′} {a} {a′} {f} {f′} {l} {l′} [B] [B′] [B≡B′]
          [∥A∥]@(noemb (∥ᵣ A' D ⊢A A≡A [A']))
          [∥B∥] [▹▹AB]
          [a≡a′]@(∥₁ₜ₌ p p′ d d′ p≅p′ (q , e , q≅q′ , z) g pa pa′ i j x) [f≡f′]
  with ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
... | PE.refl =
  transEqTerm
    [∥B∥]
    [∥ₑa≡∥ₑp]
    (transEqTerm [∥B∥] [f∘pa≡] (symEqTerm [∥B∥] [∥ₑa′≡∥ₑp″]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  ⊩f : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB]
  ⊩f = ⊩ₗ (▹▹-intr [▹▹AB]) [f≡f′]

  ⊩f′ : Γ ⊩⟨ l ⟩ f′ ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB]
  ⊩f′ = ⊩ᵣ (▹▹-intr [▹▹AB]) [f≡f′]

  [pa≡pa′] : Γ ⊩⟨ l′ ⟩ pa ≡ pa′ ∷ A / [A]
  [pa≡pa′] = irrelevanceEqTerm′ (wk-id A) ([A'] id (wf ⊢A)) [A] x

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ A / [A]
  [pa] = ⊩ₗ [A] [pa≡pa′]

  [pa′] : Γ ⊩⟨ l′ ⟩ pa′ ∷ A / [A]
  [pa′] = ⊩ᵣ [A] [pa≡pa′]

  [∥ₑa≡∥ₑp] : Γ ⊩⟨ l ⟩ ∥ₑ B a f ≡ f ∘ pa ∷ ∥ B ∥ / [∥B∥]
  [∥ₑa≡∥ₑp] = proj₂ (redSubst*Term (∥ₑ-subst*ᵢ ⊢A (escape [B])
                                                  (escapeTerm (▹▹-intr [▹▹AB]) ⊩f)
                                                  (escapeTerm [A] [pa])
                                                  (redₜ d) i)
                                    [∥B∥] (appTermNd [A] [∥B∥] (▹▹-intr [▹▹AB]) ⊩f [pa]))

  [∥B′∥] : Γ ⊩⟨ l ⟩ ∥ B′ ∥
  [∥B′∥] = {!!}

  [∥B≡B′∥] : Γ ⊩⟨ l ⟩ ∥ B ∥ ≡ ∥ B′ ∥ / [∥B∥]
  [∥B≡B′∥] = {!!}

  [▹▹AB′] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ ∥ B′ ∥
  [▹▹AB′] = ≡⊩▹▹ {Γ = Γ} {l} {A} {∥ B ∥} {∥ B′ ∥} [∥B′∥] [▹▹AB]

  [▹▹AB≡′] : Γ ⊩⟨ l ⟩ A ▹▹ ∥ B ∥ ≡ A ▹▹ ∥ B′ ∥ / ▹▹-intr [▹▹AB]
  [▹▹AB≡′] = ⊩▹▹-cong [A] [∥B∥] [∥B′∥] [∥B≡B′∥] [▹▹AB]

  ⊩f″ : Γ ⊩⟨ l ⟩ f′ ∷ A ▹▹ ∥ B′ ∥ / ▹▹-intr [▹▹AB′]
  ⊩f″ = convTerm₁ (▹▹-intr [▹▹AB]) (▹▹-intr [▹▹AB′]) [▹▹AB≡′] ⊩f′

  ⊢∥ₑa′ : Γ ⊢ ∥ₑ B′ a′ f′ ⇒* f′ ∘ pa′ ∷ ∥ B′ ∥
  ⊢∥ₑa′ = ∥ₑ-subst*ᵢ ⊢A (escape [B′])
                        (escapeTerm (▹▹-intr [▹▹AB′]) ⊩f″)
                        (escapeTerm [A] [pa′])
                        (redₜ d′) j

  [∥ₑa′≡∥ₑp″] : Γ ⊩⟨ l ⟩ ∥ₑ B′ a′ f′ ≡ f′ ∘ pa′ ∷ ∥ B ∥ / [∥B∥]
  [∥ₑa′≡∥ₑp″] = convEqTerm₂ [∥B∥] [∥B′∥] [∥B≡B′∥]
                                  (proj₂ (redSubst*Term ⊢∥ₑa′ [∥B′∥] (appTermNd [A] [∥B′∥] (▹▹-intr [▹▹AB′]) ⊩f″ [pa′])))

  [f∘pa≡] : Γ ⊩⟨ l ⟩ f ∘ pa ≡ f′ ∘ pa′ ∷ ∥ B ∥ / [∥B∥]
  [f∘pa≡] = app-congTermNd [A] [∥B∥] (▹▹-intr [▹▹AB]) [f≡f′] [pa] [pa′] [pa≡pa′]
∥ₑ-cong′ {Γ = Γ} {A = A} {B = B} {B′ = B′} {a} {a′} {f} {f′} {l} {l′} [B] [B′] [B≡B′]
          [∥A∥]@(noemb (∥ᵣ A' D ⊢A A≡A [A']))
          [∥B∥] [▹▹AB]
          [a≡a′]@(∥₂ₜ₌ p p′ d d′ p≅p′ e g (neNfₜ₌ neK neK′ k≡k)) [f≡f′]
  with ∥-PE-injectivity (whnfRed* (red D) ∥ₙ)
... | PE.refl =
  {!!} --transEqTerm [C] [∥ₑt≡∥ₑp] (transEqTerm [C] [∥ₑp≡∥ₑp′] (symEqTerm [C] [∥ₑt′≡∥ₑp′]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

{--
  [u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u] = ⊩ₗ (▹▹-intr [▹▹AC]) [u≡u′]

  [v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v] = ⊩ₗ (▹▹-intr [▹▹BC]) [v≡v′]

  [u′] : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u′] = ⊩ᵣ (▹▹-intr [▹▹AC]) [u≡u′]

  [v′] : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v′] = ⊩ᵣ (▹▹-intr [▹▹BC]) [v≡v′]

  nc : Neutral (∥ₑ C p u v)
  nc = ∥ₑₙ neK

  nc′ : Neutral (∥ₑ C′ p′ u′ v′)
  nc′ = ∥ₑₙ neK′

  ⊢C : Γ ⊢ C
  ⊢C = escape [C]

  ⊢C≅C′ : Γ ⊢ C ≅ C′
  ⊢C≅C′ = escapeEq [C] [C≡C′]

  ⊢C≡C′ : Γ ⊢ C ≡ C′
  ⊢C≡C′ = ≅-eq ⊢C≅C′

  ⊢C≅C : Γ ⊢ C ≅ C
  ⊢C≅C = ≅-trans ⊢C≅C′ (≅-sym ⊢C≅C′)

  ⊢C′≅C′ : Γ ⊢ C′ ≅ C′
  ⊢C′≅C′ = ≅-trans (≅-sym ⊢C≅C′) ⊢C≅C′

  redc : Γ ⊢ ∥ₑ C t u v ⇒* ∥ₑ C p u v ∷ C
  redc = ∥ₑ-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u]) (escapeTerm (▹▹-intr [▹▹BC]) [v]) (redₜ d)

  [▹▹AC′] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C′
  [▹▹AC′] = ≡⊩▹▹ {Γ = Γ} {l} {A} {C} {C′} [C′] [▹▹AC]

  [▹▹BC′] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C′
  [▹▹BC′] = ≡⊩▹▹ {Γ = Γ} {l} {B} {C} {C′} [C′] [▹▹BC]

  [▹▹AC≡′] : Γ ⊩⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / ▹▹-intr [▹▹AC]
  [▹▹AC≡′] = ⊩▹▹-cong [A] [C] [C′] [C≡C′] [▹▹AC]

  [▹▹BC≡′] : Γ ⊩⟨ l ⟩ B ▹▹ C ≡ B ▹▹ C′ / ▹▹-intr [▹▹BC]
  [▹▹BC≡′] = ⊩▹▹-cong [B] [C] [C′] [C≡C′] [▹▹BC]

  ⊩u″ : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C′ / ▹▹-intr [▹▹AC′]
  ⊩u″ = convTerm₁ (▹▹-intr [▹▹AC]) (▹▹-intr [▹▹AC′]) [▹▹AC≡′] [u′]

  ⊩v″ : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C′ / ▹▹-intr [▹▹BC′]
  ⊩v″ = convTerm₁ (▹▹-intr [▹▹BC]) (▹▹-intr [▹▹BC′]) [▹▹BC≡′] [v′]

  redc′ : Γ ⊢ ∥ₑ C′ t′ u′ v′ ⇒* ∥ₑ C′ p′ u′ v′ ∷ C′
  redc′ = ∥ₑ-subst* ⊢A ⊢B (escape [C′]) (escapeTerm (▹▹-intr [▹▹AC′]) ⊩u″) (escapeTerm (▹▹-intr [▹▹BC′]) ⊩v″) (redₜ d′)

  ⊢c : Γ ⊢ ∥ₑ C p u v ∷ C
  ⊢c = redSecond*Term redc

  ⊢c′ : Γ ⊢ ∥ₑ C′ p′ u′ v′ ∷ C′
  ⊢c′ = redSecond*Term redc′

  ⊢c″ : Γ ⊢ ∥ₑ C′ p′ u′ v′ ∷ C
  ⊢c″ = conv ⊢c′ (sym ⊢C≡C′)

  vc : Γ ⊩⟨ l ⟩ ∥ₑ C p u v ∷ C / [C]
  vc = neuTerm [C] nc ⊢c (~-∥ₑ ⊢A ⊢B ⊢C≅C (~-trans k≡k (~-sym k≡k))
                                  (escapeTermEq (▹▹-intr [▹▹AC]) (reflEqTerm (▹▹-intr [▹▹AC]) [u]))
                                  (escapeTermEq (▹▹-intr [▹▹BC]) (reflEqTerm (▹▹-intr [▹▹BC]) [v])))

  vc′ : Γ ⊩⟨ l ⟩ ∥ₑ C′ p′ u′ v′ ∷ C′ / [C′]
  vc′ = neuTerm [C′] nc′ ⊢c′ (~-∥ₑ ⊢A ⊢B ⊢C′≅C′ (~-trans (~-sym k≡k) k≡k)
                                      (escapeTermEq (▹▹-intr [▹▹AC′]) (reflEqTerm (▹▹-intr [▹▹AC′]) ⊩u″))
                                      (escapeTermEq (▹▹-intr [▹▹BC′]) (reflEqTerm (▹▹-intr [▹▹BC′]) ⊩v″)))

  [∥ₑt≡∥ₑp] : Γ ⊩⟨ l ⟩ ∥ₑ C t u v ≡ ∥ₑ C p u v ∷ C / [C]
  [∥ₑt≡∥ₑp] = proj₂ (redSubst*Term redc [C] vc)

  [∥ₑt′≡∥ₑp′] : Γ ⊩⟨ l ⟩ ∥ₑ C′ t′ u′ v′ ≡ ∥ₑ C′ p′ u′ v′ ∷ C / [C]
  [∥ₑt′≡∥ₑp′] = convEqTerm₂ [C] [C′] [C≡C′] (proj₂ (redSubst*Term redc′ [C′] vc′))

  [∥ₑp≡∥ₑp′] : Γ ⊩⟨ l ⟩ ∥ₑ C p u v ≡ ∥ₑ C′ p′ u′ v′ ∷ C / [C]
  [∥ₑp≡∥ₑp′] = neuEqTerm [C] nc nc′ ⊢c ⊢c″
                       (~-∥ₑ ⊢A ⊢B ⊢C≅C′ k≡k (escapeTermEq (▹▹-intr [▹▹AC]) [u≡u′])
                                                (escapeTermEq (▹▹-intr [▹▹BC]) [v≡v′]))
--}
∥ₑ-cong′ [B] [B′] [B≡B′] (emb 0<1 x) [∥B∥] [▹▹AB] [a≡a′] [f≡f′] =
  ∥ₑ-cong′ [B] [B′] [B≡B′] x [∥B∥] [▹▹AB] [a≡a′] [f≡f′]

{--
∥ₑ-cong″ : ∀ {A B C C′ t t′ u u′ v v′ l l′}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([C′]   : Γ ⊩⟨ l ⟩ C′)
            ([C≡C′] : Γ ⊩⟨ l ⟩ C ≡ C′ / [C])
            ([∪AB]  : Γ ⊩⟨ l′ ⟩ A ∪ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ A ∪ B / [∪AB])
            ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [▹▹AC])
            ([v≡v'] : Γ ⊩⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ ∥ₑ C t u v ≡ ∥ₑ C′ t′ u′ v′ ∷ C / [C]
∥ₑ-cong″ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {t} {t′} {u} {u′} {v} {v′} {l} {l′}
            [C] [C′] [C≡C′] [∪AB] [▹▹AC] [▹▹BC] [t≡t′]
            [u≡u′] [v≡v′] =
  ∥ₑ-cong′ [C] [C′] [C≡C′] (∪-elim [∪AB]) (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC])
              (irrelevanceEqTerm [∪AB] (∪-intr (∪-elim [∪AB])) [t≡t′])
              (irrelevanceEqTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u≡u′])
              (irrelevanceEqTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v≡v′])

⊩wk-from-⊩subst : {n : Nat} {Γ : Con Term n} {A : Term n} {l : TypeLevel} ([Γ] : ⊩ᵛ Γ)
                  {k : Nat} {Δ : Con Term k} {σ : Subst k n} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                → ({k : Nat} {Δ : Con Term k} {σ : Subst k n} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Δ ⊩⟨ l ⟩ subst σ A)
                → {m : Nat} {ρ : Wk m k} {Δ′ : Con Term m} → ρ ∷ Δ′ ⊆ Δ → ⊢ Δ′ → Δ′ ⊩⟨ l ⟩ U.wk ρ (subst σ A)
⊩wk-from-⊩subst {n = n} {Γ} {A} {l} [Γ] {k} {Δ} {σ} ⊢Δ [σ] h {m} {ρ} {Δ′} [ρ] ⊢Δ′ =
  PE.subst (λ x → Δ′ ⊩⟨ l ⟩ x) (PE.sym (wk-subst A)) q
  where
  σ₁ : Subst m n
  σ₁ = ρ •ₛ σ

  [σ₁] : Δ′ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ′
  [σ₁] = wkSubstS [Γ] ⊢Δ ⊢Δ′ [ρ] [σ]

  q : Δ′ ⊩⟨ l ⟩ subst σ₁ A
  q = h {m} {Δ′} {σ₁} ⊢Δ′ [σ₁]

-- Validity of ∥ₑ
∥ₑᵛ : ∀ {Γ : Con Term n} {A B C t u v l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
         ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
         ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
         → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ C t u v ∷ C / [Γ] / [C]
∥ₑᵛ {Γ = Γ} {A} {B} {C} {t} {u} {v} {l} [Γ] [A] [B] [C] [t] [u] [v] {k = k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB]  = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      σ∥ₑ : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → Δ ⊩⟨ l ⟩ subst σ (∥ₑ C t u v) ∷ subst σ C / proj₁ ([C] ⊢Δ [σ])
      σ∥ₑ {Δ} {σ} ⊢Δ [σ] =
        let ⊩σC    = proj₁ ([C] ⊢Δ [σ])
            ⊩σ∪AB  = proj₁ ([∪AB] ⊢Δ [σ])
            ⊩σ▹▹AC = proj₁ ([▹▹AC] ⊢Δ [σ])
            ⊩σ▹▹BC = proj₁ ([▹▹BC] ⊢Δ [σ])
            ⊩σt    = proj₁ ([t] ⊢Δ [σ])
            ⊩σu    = proj₁ ([u] ⊢Δ [σ])
            ⊩σv    = proj₁ ([v] ⊢Δ [σ])
        in ∥ₑ″ ⊩σC ⊩σ∪AB
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                  ⊩σt
                  (irrelevanceTerm′ (subst▹▹ σ A C)
                                    (proj₁ (▹▹ᵛ {_} {Γ} {A} {C} [Γ] [A] [C] ⊢Δ [σ]))
                                    (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                                    ⊩σu)
                  (irrelevanceTerm′ (subst▹▹ σ B C)
                                    (proj₁ (▹▹ᵛ {_} {Γ} {B} {C} [Γ] [B] [C] ⊢Δ [σ]))
                                    (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                                    ⊩σv)
  in  σ∥ₑ ⊢Δ [σ] ,
      λ {σ′} [σ′] [σ≡σ′] →
        let [σC]     = proj₁ ([C] ⊢Δ [σ])
            [σC′]    = proj₁ ([C] ⊢Δ [σ′])
            [σC≡C′]  = proj₂ ([C] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σ∪AB]   = proj₁ ([∪AB] ⊢Δ [σ])
            [σ▹▹AC]  = proj₁ ([▹▹AC] ⊢Δ [σ])
            [σ▹▹BC]  = proj₁ ([▹▹BC] ⊢Δ [σ])
            [σt]     = proj₁ ([t] ⊢Δ [σ])
            [σt≡t′]  = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σu≡u′]  = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σv≡v′]  = proj₂ ([v] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  ∥ₑ-cong″ [σC] [σC′] [σC≡C′] [σ∪AB]
                        (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) [σ▹▹AC])
                        (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) [σ▹▹BC])
                        [σt≡t′]
                        (irrelevanceEqTerm′ (subst▹▹ σ A C)
                                            (proj₁ (▹▹ᵛ {_} {Γ} {A} {C} [Γ] [A] [C] ⊢Δ [σ]))
                                            (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) [σ▹▹AC])
                                            [σu≡u′])
                        (irrelevanceEqTerm′ (subst▹▹ σ B C)
                                            (proj₁ (▹▹ᵛ {_} {Γ} {B} {C} [Γ] [B] [C] ⊢Δ [σ]))
                                            (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) [σ▹▹BC])
                                            [σv≡v′])

∥ₑ-congᵛ : ∀ {n : Nat} {Γ : Con Term n} {A B C C′ t t′ u u′ v v′ l}
              ([Γ]    : ⊩ᵛ Γ)
              ([A]    : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([B]    : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
              ([C]    : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
              ([C′]   : Γ ⊩ᵛ⟨ l ⟩ C′ / [Γ])
              ([C≡C′] : Γ ⊩ᵛ⟨ l ⟩ C ≡ C′ / [Γ] / [C])
              ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
              ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
              ([v≡v'] : Γ ⊩ᵛ⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ C t u v ≡ ∥ₑ C′ t′ u′ v′ ∷ C / [Γ] / [C]
∥ₑ-congᵛ {n = n} {Γ = Γ} {A} {B} {C} {C′} {t} {t′} {u} {u′} {v} {v′} {l}
            [Γ] [A] [B] [C] [C′] [C≡C′] [t≡t′] [u≡u′] [v≡v′] {k = k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB]  = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      ⊩σC    = proj₁ ([C] ⊢Δ [σ])
      ⊩σC′   = proj₁ ([C′] ⊢Δ [σ])
      ⊩σ∪AB  = proj₁ ([∪AB] ⊢Δ [σ])
      ⊩σ▹▹AC = proj₁ ([▹▹AC] ⊢Δ [σ])
      ⊩σ▹▹BC = proj₁ ([▹▹BC] ⊢Δ [σ])
      ⊩σC≡C′ = [C≡C′] ⊢Δ [σ]
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
      ⊩σu≡u′ = [u≡u′] ⊢Δ [σ]
      ⊩σv≡v′ = [v≡v′] ⊢Δ [σ]
  in  ∥ₑ-cong″ ⊩σC ⊩σC′ ⊩σC≡C′ ⊩σ∪AB
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                  ⊩σt≡t′
                  (irrelevanceEqTerm′ (subst▹▹ σ A C)
                                      (proj₁ (▹▹ᵛ {_} {Γ} {A} {C} [Γ] [A] [C] ⊢Δ [σ]))
                                      (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                                      ⊩σu≡u′)
                  (irrelevanceEqTerm′ (subst▹▹ σ B C)
                                      (proj₁ (▹▹ᵛ {_} {Γ} {B} {C} [Γ] [B] [C] ⊢Δ [σ]))
                                      (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                                      ⊩σv≡v′)

∥ₑ-βₗ′ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ A / [A])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ ∥ₑ C (injl t) u v ≡ u ∘ t ∷ C / [C]
∥ₑ-βₗ′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  proj₂ (redSubst*Term (∥ₑ-subst*ₗ (escape [A]) (escape [B]) (escape [C])
                                      (escapeTerm (▹▹-intr [▹▹AC]) [u])
                                      (escapeTerm (▹▹-intr [▹▹BC]) [v])
                                      (escapeTerm [A] [t])
                                      (id (injlⱼ (escapeTerm [A] [t]) (escape [B]))) injlₙ)
                       [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) [u] [t]))

∥ₑ-βₗ″ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ A / [A])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ ∥ₑ C (injl t) u v ≡ u ∘ t ∷ C / [C]
∥ₑ-βₗ″ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  ∥ₑ-βₗ′ [C] [A] [B] (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC]) [t]
            (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
            (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

∥ₑ-βₗᵛ : ∀ {A B C t u v l}
            ([Γ] : ⊩ᵛ Γ)
            ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
            ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
            ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ C (injl t) u v ≡ u ∘ t ∷ C / [Γ] / [C]
∥ₑ-βₗᵛ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [Γ] [C] [A] [B] [t] [u] [v] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      ⊩σA    = proj₁ ([A] ⊢Δ [σ])
      ⊩σB    = proj₁ ([B] ⊢Δ [σ])
      ⊩σC    = proj₁ ([C] ⊢Δ [σ])
      ⊩σ▹▹AC = proj₁ ([▹▹AC] ⊢Δ [σ])
      ⊩σ▹▹BC = proj₁ ([▹▹BC] ⊢Δ [σ])
      ⊩σt    = proj₁ ([t] ⊢Δ [σ])
      ⊩σu    = proj₁ ([u] ⊢Δ [σ])
      ⊩σv    = proj₁ ([v] ⊢Δ [σ])
  in ∥ₑ-βₗ″ ⊩σC ⊩σA ⊩σB
               (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
               (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
               ⊩σt
               (irrelevanceTerm′ (subst▹▹ σ A C)
                                 (proj₁ (▹▹ᵛ {_} {Γ} {A} {C} [Γ] [A] [C] ⊢Δ [σ]))
                                 (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                                 ⊩σu)
               (irrelevanceTerm′ (subst▹▹ σ B C)
                                 (proj₁ (▹▹ᵛ {_} {Γ} {B} {C} [Γ] [B] [C] ⊢Δ [σ]))
                                 (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                                 ⊩σv)

∥ₑ-βᵣ′ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ B / [B])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ ∥ₑ C (injr t) u v ≡ v ∘ t ∷ C / [C]
∥ₑ-βᵣ′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  proj₂ (redSubst*Term (∥ₑ-subst*ᵣ (escape [A]) (escape [B]) (escape [C])
                                      (escapeTerm (▹▹-intr [▹▹AC]) [u])
                                      (escapeTerm (▹▹-intr [▹▹BC]) [v])
                                      (escapeTerm [B] [t])
                                      (id (injrⱼ (escape [A]) (escapeTerm [B] [t]))) injrₙ)
                       [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) [v] [t]))

∥ₑ-βᵣ″ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ B / [B])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ ∥ₑ C (injr t) u v ≡ v ∘ t ∷ C / [C]
∥ₑ-βᵣ″ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  ∥ₑ-βᵣ′ [C] [A] [B] (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC]) [t]
            (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
            (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

∥ₑ-βᵣᵛ : ∀ {A B C t u v l}
            ([Γ] : ⊩ᵛ Γ)
            ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
            ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B])
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
            ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ C (injr t) u v ≡ v ∘ t ∷ C / [Γ] / [C]
∥ₑ-βᵣᵛ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [Γ] [C] [A] [B] [t] [u] [v] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      ⊩σA    = proj₁ ([A] ⊢Δ [σ])
      ⊩σB    = proj₁ ([B] ⊢Δ [σ])
      ⊩σC    = proj₁ ([C] ⊢Δ [σ])
      ⊩σ▹▹AC = proj₁ ([▹▹AC] ⊢Δ [σ])
      ⊩σ▹▹BC = proj₁ ([▹▹BC] ⊢Δ [σ])
      ⊩σt    = proj₁ ([t] ⊢Δ [σ])
      ⊩σu    = proj₁ ([u] ⊢Δ [σ])
      ⊩σv    = proj₁ ([v] ⊢Δ [σ])
  in ∥ₑ-βᵣ″ ⊩σC ⊩σA ⊩σB
               (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
               (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
               ⊩σt
               (irrelevanceTerm′ (subst▹▹ σ A C)
                                 (proj₁ (▹▹ᵛ {_} {Γ} {A} {C} [Γ] [A] [C] ⊢Δ [σ]))
                                 (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A C) ⊩σ▹▹AC)
                                 ⊩σu)
               (irrelevanceTerm′ (subst▹▹ σ B C)
                                 (proj₁ (▹▹ᵛ {_} {Γ} {B} {C} [Γ] [B] [C] ⊢Δ [σ]))
                                 (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ B C) ⊩σ▹▹BC)
                                 ⊩σv)
--}
