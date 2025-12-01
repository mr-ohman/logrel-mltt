{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

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
  using (▹▹∘ⱼ ; appTermNd ; redSecond*Term ; ⊩ₗ ; ⊩ᵣ ; ≡⊩▹▹ ; ⊩▹▹-cong ; app-congTermNd ; subst▹▹)
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
  ⇨∷* (∥-β ⊢B ⊢x ⊢f
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
  vc = neuTerm [∥B∥] nc ⊢c (~-∥ₑ ⊢A (escapeEq [B] (reflEq [B]))
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

:⇒*:-refl : ∀ {B}
          → Γ ⊢ B
          → Γ ⊢ ∥ B ∥ :⇒*: ∥ B ∥
:⇒*:-refl {B} ⊢B = [ ∥ ⊢B ∥ⱼ , ∥ ⊢B ∥ⱼ , id ∥ ⊢B ∥ⱼ ]

⇒*-refl : ∀ {B}
        → Γ ⊢ B
        → Γ ⊢ ∥ B ∥ ⇒* ∥ B ∥
⇒*-refl {B} ⊢B = id ∥ ⊢B ∥ⱼ

⊩-mon : ∀ {n} {Γ : Con Term n} {B l}
      → Γ ⊩⟨ l ⟩ B
      → {m : Nat} {ρ : Wk m n} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ → Δ ⊩⟨ l ⟩ U.wk ρ B
⊩-mon {n = n} {Γ = Γ} {B = B} {l = l} h {m} {ρ} {Δ} [ρ] ⊢Δ = wk [ρ] ⊢Δ h

⊩∥ : ∀ {n} {Γ : Con Term n} {B l}
     → Γ ⊩⟨ l ⟩ B
     → Γ ⊩⟨ l ⟩ ∥ B ∥
⊩∥ {n = n} {Γ = Γ} {B = B} {l = l} h =
  ∥ᵣ (∥ᵣ B (:⇒*:-refl (escape h)) (escape h) (≅-∥-cong (escapeEq h (reflEq h))) (⊩-mon h))

⊩≡∥ : ∀ {n} {Γ : Con Term n} {A B l}
        ([A]   : Γ ⊩⟨ l ⟩ A)
        ([B]   : Γ ⊩⟨ l ⟩ B)
        ([∥A∥] : Γ ⊩⟨ l ⟩ ∥ A ∥)
     → Γ ⊩⟨ l ⟩ A ≡ B / [A]
     → Γ ⊩⟨ l ⟩ ∥ A ∥ ≡ ∥ B ∥ / [∥A∥]
⊩≡∥ {n = n} {Γ = Γ} {A = A} {B = B} {l = l} [A] [B] [∥A∥] h =
  irrelevanceEq′
    PE.refl (⊩∥ [A]) [∥A∥]
    (∥₌ B (⇒*-refl ⊢B) (≅-∥-cong (escapeEq [A] h)) q)
  where
  ⊢B : Γ ⊢ B
  ⊢B = escape [B]

  A≡B : Γ ⊢ A ≡ B
  A≡B = ≅-eq (escapeEq [A] h)

  q : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
    → Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ B / (⊩-mon [A] [ρ] ⊢Δ)
  q {m} {ρ} {Δ} [ρ] ⊢Δ = wkEq [ρ] ⊢Δ [A] h

⊩ᵛ∥ : ∀ {Γ : Con Term n} {A l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
      → Γ ⊩ᵛ⟨ l ⟩ ∥ A ∥ / [Γ]
⊩ᵛ∥ {n} {Γ} {A} {l} [Γ] h {k} {Δ} {σ} ⊢Δ [σ]
  with h ⊢Δ [σ]
... | ⊢A , ⊢≡A =
  ⊩∥ ⊢A ,
  λ {σ′} [σ′] [σ≡σ′] → ⊩≡∥ {Γ = Δ} {A = subst σ A} {B = subst σ′ A} ⊢A (proj₁ (h ⊢Δ [σ′])) (⊩∥ ⊢A) (⊢≡A [σ′] [σ≡σ′])

⊩≡ᵛ∥ : ∀ {Γ : Con Term n} {A B l}
        ([Γ]   : ⊩ᵛ Γ)
        ([A]   : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([B]   : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
        ([∥A∥] : Γ ⊩ᵛ⟨ l ⟩ ∥ A ∥ / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ ∥ A ∥ ≡ ∥ B ∥ / [Γ] / [∥A∥]
⊩≡ᵛ∥ {n} {Γ} {A} {B} {l} [Γ] [A] [B] [∥A∥] h {k} {Δ} {σ} ⊢Δ [σ] =
  ⊩≡∥ {Γ = Δ} {A = subst σ A} {B = subst σ B}
      (proj₁ ([A] ⊢Δ [σ]))
      (proj₁ ([B] ⊢Δ [σ]))
      (proj₁ ([∥A∥] ⊢Δ [σ]))
      (h ⊢Δ [σ])

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
  [∥B′∥] = ⊩∥ [B′]

  [∥B≡B′∥] : Γ ⊩⟨ l ⟩ ∥ B ∥ ≡ ∥ B′ ∥ / [∥B∥]
  [∥B≡B′∥] = ⊩≡∥ [B] [B′] [∥B∥] [B≡B′]

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
  transEqTerm [∥B∥] [∥ₑa≡∥ₑp] (transEqTerm [∥B∥] [∥ₑp≡∥ₑp′] (symEqTerm [∥B∥] [∥ₑa′≡∥ₑp′]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  [f] : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB]
  [f] = ⊩ₗ (▹▹-intr [▹▹AB]) [f≡f′]

  [f′] : Γ ⊩⟨ l ⟩ f′ ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB]
  [f′] = ⊩ᵣ (▹▹-intr [▹▹AB]) [f≡f′]

  nc : Neutral (∥ₑ B p f)
  nc = ∥ₑₙ neK

  nc′ : Neutral (∥ₑ B′ p′ f′)
  nc′ = ∥ₑₙ neK′

  ⊢B : Γ ⊢ B
  ⊢B = escape [B]

  ⊢B≅B′ : Γ ⊢ B ≅ B′
  ⊢B≅B′ = escapeEq [B] [B≡B′]

  ⊢B≡B′ : Γ ⊢ B ≡ B′
  ⊢B≡B′ = ≅-eq ⊢B≅B′

  ⊢B≅B : Γ ⊢ B ≅ B
  ⊢B≅B = ≅-trans ⊢B≅B′ (≅-sym ⊢B≅B′)

  ⊢B′≅B′ : Γ ⊢ B′ ≅ B′
  ⊢B′≅B′ = ≅-trans (≅-sym ⊢B≅B′) ⊢B≅B′

  redc : Γ ⊢ ∥ₑ B a f ⇒* ∥ₑ B p f ∷ ∥ B ∥
  redc = ∥ₑ-subst* ⊢A ⊢B (escapeTerm (▹▹-intr [▹▹AB]) [f]) (redₜ d)

  [∥B′∥] : Γ ⊩⟨ l ⟩ ∥ B′ ∥
  [∥B′∥] = ⊩∥ [B′]

  [∥B≡B′∥] : Γ ⊩⟨ l ⟩ ∥ B ∥ ≡ ∥ B′ ∥ / [∥B∥]
  [∥B≡B′∥] = ⊩≡∥ [B] [B′] [∥B∥] [B≡B′]

  ⊢B′ : Γ ⊢ B′
  ⊢B′ = escape [B′]

  ⊢∥B≡B′∥ : Γ ⊢ ∥ B ∥ ≡ ∥ B′ ∥
  ⊢∥B≡B′∥ = ∥-cong ⊢B≡B′

  [▹▹AB′] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ ∥ B′ ∥
  [▹▹AB′] = ≡⊩▹▹ {Γ = Γ} {l} {A} {∥ B ∥} {∥ B′ ∥} [∥B′∥] [▹▹AB]

  [▹▹AB≡′] : Γ ⊩⟨ l ⟩ A ▹▹ ∥ B ∥ ≡ A ▹▹ ∥ B′ ∥ / ▹▹-intr [▹▹AB]
  [▹▹AB≡′] = ⊩▹▹-cong [A] [∥B∥] [∥B′∥] [∥B≡B′∥] [▹▹AB]

  ⊩f″ : Γ ⊩⟨ l ⟩ f′ ∷ A ▹▹ ∥ B′ ∥ / ▹▹-intr [▹▹AB′]
  ⊩f″ = convTerm₁ (▹▹-intr [▹▹AB]) (▹▹-intr [▹▹AB′]) [▹▹AB≡′] [f′]

  redc′ : Γ ⊢ ∥ₑ B′ a′ f′ ⇒* ∥ₑ B′ p′ f′ ∷ ∥ B′ ∥
  redc′ = ∥ₑ-subst* ⊢A ⊢B′ (escapeTerm (▹▹-intr [▹▹AB′]) ⊩f″) (redₜ d′)

  ⊢c : Γ ⊢ ∥ₑ B p f ∷ ∥ B ∥
  ⊢c = redSecond*Term redc

  ⊢c′ : Γ ⊢ ∥ₑ B′ p′ f′ ∷ ∥ B′ ∥
  ⊢c′ = redSecond*Term redc′

  ⊢c″ : Γ ⊢ ∥ₑ B′ p′ f′ ∷ ∥ B ∥
  ⊢c″ = conv ⊢c′ (sym ⊢∥B≡B′∥)

  vc : Γ ⊩⟨ l ⟩ ∥ₑ B p f ∷ ∥ B ∥ / [∥B∥]
  vc = neuTerm [∥B∥] nc ⊢c (~-∥ₑ ⊢A ⊢B≅B (~-trans k≡k (~-sym k≡k))
                                 (escapeTermEq (▹▹-intr [▹▹AB]) (reflEqTerm (▹▹-intr [▹▹AB]) [f])))

  vc′ : Γ ⊩⟨ l ⟩ ∥ₑ B′ p′ f′ ∷ ∥ B′ ∥ / [∥B′∥]
  vc′ = neuTerm [∥B′∥] nc′ ⊢c′ (~-∥ₑ ⊢A ⊢B′≅B′ (~-trans (~-sym k≡k) k≡k)
                                     (escapeTermEq (▹▹-intr [▹▹AB′]) (reflEqTerm (▹▹-intr [▹▹AB′]) ⊩f″)))

  [∥ₑa≡∥ₑp] : Γ ⊩⟨ l ⟩ ∥ₑ B a f ≡ ∥ₑ B p f ∷ ∥ B ∥ / [∥B∥]
  [∥ₑa≡∥ₑp] = proj₂ (redSubst*Term redc [∥B∥] vc)

  [∥ₑa′≡∥ₑp′] : Γ ⊩⟨ l ⟩ ∥ₑ B′ a′ f′ ≡ ∥ₑ B′ p′ f′ ∷ ∥ B ∥ / [∥B∥]
  [∥ₑa′≡∥ₑp′] = convEqTerm₂ [∥B∥] [∥B′∥] [∥B≡B′∥] (proj₂ (redSubst*Term redc′ [∥B′∥] vc′))

  [∥ₑp≡∥ₑp′] : Γ ⊩⟨ l ⟩ ∥ₑ B p f ≡ ∥ₑ B′ p′ f′ ∷ ∥ B ∥ / [∥B∥]
  [∥ₑp≡∥ₑp′] = neuEqTerm [∥B∥] nc nc′ ⊢c ⊢c″
                         (~-∥ₑ ⊢A ⊢B≅B′ k≡k (escapeTermEq (▹▹-intr [▹▹AB]) [f≡f′]))
∥ₑ-cong′ [B] [B′] [B≡B′] (emb 0<1 x) [∥B∥] [▹▹AB] [a≡a′] [f≡f′] =
  ∥ₑ-cong′ [B] [B′] [B≡B′] x [∥B∥] [▹▹AB] [a≡a′] [f≡f′]

∥ₑ-cong″ : ∀ {A B B′ a a′ f f′ l l′}
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([B′]   : Γ ⊩⟨ l ⟩ B′)
            ([B≡B′] : Γ ⊩⟨ l ⟩ B ≡ B′ / [B])
            ([∥A∥]  : Γ ⊩⟨ l′ ⟩ ∥ A ∥)
            ([∥B∥]  : Γ ⊩⟨ l ⟩ ∥ B ∥)
            ([▹▹AB] : Γ ⊩⟨ l ⟩ A ▹▹ ∥ B ∥)
            ([a≡a′] : Γ ⊩⟨ l′ ⟩ a ≡ a′ ∷ ∥ A ∥ / [∥A∥])
            ([f≡f′] : Γ ⊩⟨ l ⟩ f ≡ f′ ∷ A ▹▹ ∥ B ∥ / [▹▹AB])
            → Γ ⊩⟨ l ⟩ ∥ₑ B a f ≡ ∥ₑ B′ a′ f′ ∷ ∥ B ∥ / [∥B∥]
∥ₑ-cong″ {Γ = Γ} {A = A} {B = B} {B′ = B′} {a} {a′} {f} {f′} {l} {l′}
            [B] [B′] [B≡B′] [∥A∥] [∥B∥] [▹▹AB] [a≡a′] [f≡f′] =
  ∥ₑ-cong′ [B] [B′] [B≡B′] (∥-elim [∥A∥]) [∥B∥] (▹▹-elim [▹▹AB])
              (irrelevanceEqTerm [∥A∥] (∥-intr (∥-elim [∥A∥])) [a≡a′])
              (irrelevanceEqTerm [▹▹AB] (▹▹-intr (▹▹-elim [▹▹AB])) [f≡f′])

-- Validity of ∥ₑ
∥ₑᵛ : ∀ {Γ : Con Term n} {A B a f l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         ([∥B∥] : Γ ⊩ᵛ⟨ l ⟩ ∥ B ∥ / [Γ])
         ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ ∥ A ∥ / [Γ] / ∥ᵛ {F = A} [Γ] [A])
         ([f] : Γ ⊩ᵛ⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / [Γ] / ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥])
         → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ B a f ∷ ∥ B ∥ / [Γ] / [∥B∥]
∥ₑᵛ {Γ = Γ} {A} {B} {a} {f} {l} [Γ] [A] [B] [∥B∥] [a] [f] {k = k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∥A∥]  = ∥ᵛ {F = A} [Γ] [A]
      [▹▹AB] = ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]
      σ∥ₑ : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → Δ ⊩⟨ l ⟩ subst σ (∥ₑ B a f) ∷ subst σ (∥ B ∥) / proj₁ ([∥B∥] ⊢Δ [σ])
      σ∥ₑ {Δ} {σ} ⊢Δ [σ] =
        let ⊩σB    = proj₁ ([B] ⊢Δ [σ])
            ⊩σ∥B∥  = proj₁ ([∥B∥] ⊢Δ [σ])
            ⊩σ∥A∥  = proj₁ ([∥A∥] ⊢Δ [σ])
            ⊩σ▹▹AB = proj₁ ([▹▹AB] ⊢Δ [σ])
            ⊩σa    = proj₁ ([a] ⊢Δ [σ])
            ⊩σf    = proj₁ ([f] ⊢Δ [σ])
        in ∥ₑ″ ⊩σB ⊩σ∥A∥ ⊩σ∥B∥
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
                  ⊩σa
                  (irrelevanceTerm′ (subst▹▹ σ A ∥ B ∥)
                                    (proj₁ (▹▹ᵛ {_} {Γ} {A} {∥ B ∥} [Γ] [A] [∥B∥] ⊢Δ [σ]))
                                    (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
                                    ⊩σf)
  in  σ∥ₑ ⊢Δ [σ] ,
      λ {σ′} [σ′] [σ≡σ′] →
        let [σB]      = proj₁ ([B] ⊢Δ [σ])
            [σB′]     = proj₁ ([B] ⊢Δ [σ′])
            [σB≡B′]   = proj₂ ([B] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σ∥B∥]    = proj₁ ([∥B∥] ⊢Δ [σ])
            [σ∥B′∥]   = proj₁ ([∥B∥] ⊢Δ [σ′])
            [σ∥B≡B′∥] = proj₂ ([∥B∥] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σ∥A∥]    = proj₁ ([∥A∥] ⊢Δ [σ])
            [σ▹▹AB]   = proj₁ ([▹▹AB] ⊢Δ [σ])
            [σa]      = proj₁ ([a] ⊢Δ [σ])
            [σa≡a′]   = proj₂ ([a] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σf≡f′]   = proj₂ ([f] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  ∥ₑ-cong″ [σB] [σB′] [σB≡B′] [σ∥A∥] [σ∥B∥]
                        (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) [σ▹▹AB])
                        [σa≡a′]
                        (irrelevanceEqTerm′ (subst▹▹ σ A ∥ B ∥)
                                            (proj₁ (▹▹ᵛ {_} {Γ} {A} {∥ B ∥} [Γ] [A] [∥B∥] ⊢Δ [σ]))
                                            (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) [σ▹▹AB])
                                            [σf≡f′])

∥ₑ-congᵛ : ∀ {n : Nat} {Γ : Con Term n} {A B B′ a a′ f f′ l}
              ([Γ]    : ⊩ᵛ Γ)
              ([A]    : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([B]    : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
              ([∥B∥]  : Γ ⊩ᵛ⟨ l ⟩ ∥ B ∥ / [Γ])
              ([B′]   : Γ ⊩ᵛ⟨ l ⟩ B′ / [Γ])
              ([B≡B′] : Γ ⊩ᵛ⟨ l ⟩ B ≡ B′ / [Γ] / [B])
              ([a≡a′] : Γ ⊩ᵛ⟨ l ⟩ a ≡ a′ ∷ ∥ A ∥ / [Γ] / ∥ᵛ {F = A} [Γ] [A])
              ([f≡f′] : Γ ⊩ᵛ⟨ l ⟩ f ≡ f′ ∷ A ▹▹ ∥ B ∥ / [Γ] / ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥])
            → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ B a f ≡ ∥ₑ B′ a′ f′ ∷ ∥ B ∥ / [Γ] / [∥B∥]
∥ₑ-congᵛ {n = n} {Γ = Γ} {A} {B} {B′} {a} {a′} {f} {f′} {l}
            [Γ] [A] [B] [∥B∥] [B′] [B≡B′] [a≡a′] [f≡f′] {k = k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∥A∥]  = ∥ᵛ {F = A} [Γ] [A]
      [▹▹AB] = ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]
      ⊩σB    = proj₁ ([B] ⊢Δ [σ])
      ⊩σ∥B∥  = proj₁ ([∥B∥] ⊢Δ [σ])
      ⊩σB′   = proj₁ ([B′] ⊢Δ [σ])
      ⊩σ∥A∥  = proj₁ ([∥A∥] ⊢Δ [σ])
      ⊩σ▹▹AB = proj₁ ([▹▹AB] ⊢Δ [σ])
      ⊩σB≡B′ = [B≡B′] ⊢Δ [σ]
      ⊩σa≡a′ = [a≡a′] ⊢Δ [σ]
      ⊩σf≡f′ = [f≡f′] ⊢Δ [σ]
  in  ∥ₑ-cong″ ⊩σB ⊩σB′ ⊩σB≡B′ ⊩σ∥A∥ ⊩σ∥B∥
                  (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
                  ⊩σa≡a′
                  (irrelevanceEqTerm′ (subst▹▹ σ A ∥ B ∥)
                                      (proj₁ (▹▹ᵛ {_} {Γ} {A} {∥ B ∥} [Γ] [A] [∥B∥] ⊢Δ [σ]))
                                      (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
                                      ⊩σf≡f′)

∥ₑ-β′ : ∀ {A B a f l}
          ([A]    : Γ ⊩⟨ l ⟩ A)
          ([B]    : Γ ⊩⟨ l ⟩ B)
          ([∥B∥]    : Γ ⊩⟨ l ⟩ ∥ B ∥)
          ([▹▹AB] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ ∥ B ∥)
          ([a]    : Γ ⊩⟨ l ⟩ a ∷ A / [A])
          ([f]    : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / ▹▹-intr [▹▹AB])
        → Γ ⊩⟨ l ⟩ ∥ₑ B (∥ᵢ a) f ≡ f ∘ a ∷ ∥ B ∥ / [∥B∥]
∥ₑ-β′ {Γ = Γ} {A = A} {B = B} {a} {f} {l} [A] [B] [∥B∥] [▹▹AB] [a] [f] =
  proj₂ (redSubst*Term (∥ₑ-subst*ᵢ (escape [A]) (escape [B])
                                      (escapeTerm (▹▹-intr [▹▹AB]) [f])
                                      (escapeTerm [A] [a])
                                      (id (∥ᵢⱼ (escapeTerm [A] [a]))) ∥ᵢₙ)
                       [∥B∥] (appTermNd [A] [∥B∥] (▹▹-intr [▹▹AB]) [f] [a]))

∥ₑ-β″ : ∀ {A B a f l}
          ([A]    : Γ ⊩⟨ l ⟩ A)
          ([B]    : Γ ⊩⟨ l ⟩ B)
          ([∥B∥]  : Γ ⊩⟨ l ⟩ ∥ B ∥)
          ([▹▹AB] : Γ ⊩⟨ l ⟩ A ▹▹ ∥ B ∥)
          ([a]    : Γ ⊩⟨ l ⟩ a ∷ A / [A])
          ([f]    : Γ ⊩⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / [▹▹AB])
        → Γ ⊩⟨ l ⟩ ∥ₑ B (∥ᵢ a) f ≡ f ∘ a ∷ ∥ B ∥ / [∥B∥]
∥ₑ-β″ {Γ = Γ} {A = A} {B = B} {a} {f} {l}
      [A] [B] [∥B∥] [▹▹AB] [a] [f] =
  ∥ₑ-β′ [A] [B] [∥B∥] (▹▹-elim [▹▹AB]) [a]
            (irrelevanceTerm [▹▹AB] (▹▹-intr (▹▹-elim [▹▹AB])) [f])

∥ₑ-βᵛ : ∀ {A B a f l}
          ([Γ]   : ⊩ᵛ Γ)
          ([A]   : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
          ([B]   : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
          ([∥B∥] : Γ ⊩ᵛ⟨ l ⟩ ∥ B ∥ / [Γ])
          ([a]   : Γ ⊩ᵛ⟨ l ⟩ a ∷ A / [Γ] / [A])
          ([f]   : Γ ⊩ᵛ⟨ l ⟩ f ∷ A ▹▹ ∥ B ∥ / [Γ] / ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥])
        → Γ ⊩ᵛ⟨ l ⟩ ∥ₑ B (∥ᵢ a) f ≡ f ∘ a ∷ ∥ B ∥ / [Γ] / [∥B∥]
∥ₑ-βᵛ {Γ = Γ} {A = A} {B = B} {a} {f} {l}
       [Γ] [A] [B] [∥B∥] [a] [f] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [▹▹AB] = ▹▹ᵛ {F = A} {∥ B ∥} [Γ] [A] [∥B∥]
      ⊩σA    = proj₁ ([A] ⊢Δ [σ])
      ⊩σB    = proj₁ ([B] ⊢Δ [σ])
      ⊩σ∥B∥  = proj₁ ([∥B∥] ⊢Δ [σ])
      ⊩σ▹▹AB = proj₁ ([▹▹AB] ⊢Δ [σ])
      ⊩σa    = proj₁ ([a] ⊢Δ [σ])
      ⊩σf    = proj₁ ([f] ⊢Δ [σ])
  in ∥ₑ-β″ ⊩σA ⊩σB ⊩σ∥B∥
               (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
               ⊩σa
               (irrelevanceTerm′ (subst▹▹ σ A ∥ B ∥)
                                 (proj₁ (▹▹ᵛ {_} {Γ} {A} {∥ B ∥} [Γ] [A] [∥B∥] ⊢Δ [σ]))
                                 (PE.subst (λ x → Δ ⊩⟨ l ⟩ x) (subst▹▹ σ A ∥ B ∥) ⊩σ▹▹AB)
                                 ⊩σf)
