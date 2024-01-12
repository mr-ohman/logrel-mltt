{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation


module Definition.LogicalRelation.Substitution.Introductions.Cases {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as Wk hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.Union
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

cases-subst* : ∀ {A B C t t′ u v}
             → Γ ⊢ A
             → Γ ⊢ B
             → Γ ⊢ C
             → Γ ⊢ u ∷ A ▹▹ C
             → Γ ⊢ v ∷ B ▹▹ C
             → Γ ⊢ t ⇒* t′ ∷ A ∪ B
             → Γ ⊢ cases t u v ⇒* cases t′ u v ∷ C
cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v (id x) = id (casesⱼ x ⊢u ⊢v ⊢C)
cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v (x ⇨ t⇒t′) = cases-subst ⊢A ⊢B ⊢C ⊢u ⊢v x ⇨ cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′

▹▹∘ⱼ : ∀ {g a F G}
     → Γ ⊢     g ∷ F ▹▹ G
     → Γ ⊢     a ∷ F
     → Γ ⊢ g ∘ a ∷ G
▹▹∘ⱼ {l} {Γ} {g} {a} {F} {G} ⊢g ⊢a =
  PE.subst (λ x → Γ ⊢ g ∘ a ∷ x)
           (wk1-sgSubst G a)
           (⊢g ∘ⱼ ⊢a)

redSecond*Term : ∀ {A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ∷ A
redSecond*Term (id t) = t
redSecond*Term (t⇒t′ ⇨ t′⇒*u) = redSecond*Term t′⇒*u

cases-subst*ₗ : ∀ {A B C t t′ u v x}
              → Γ ⊢ A
              → Γ ⊢ B
              → Γ ⊢ C
              → Γ ⊢ u ∷ A ▹▹ C
              → Γ ⊢ v ∷ B ▹▹ C
              → Γ ⊢ x ∷ A
              → Γ ⊢ t ⇒* t′ ∷ A ∪ B
              → InjectionL t′ x
              → Γ ⊢ cases t u v ⇒* u ∘ x ∷ C
cases-subst*ₗ ⊢A ⊢B ⊢C ⊢u ⊢v ⊢x t⇒t′ injlₙ =
  cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′
  ⇨∷* (∪-β₁ ⊢A ⊢B ⊢C ⊢x ⊢u ⊢v
       ⇨ id (▹▹∘ⱼ ⊢u ⊢x))

cases-subst*ᵣ : ∀ {A B C t t′ u v x}
              → Γ ⊢ A
              → Γ ⊢ B
              → Γ ⊢ C
              → Γ ⊢ u ∷ A ▹▹ C
              → Γ ⊢ v ∷ B ▹▹ C
              → Γ ⊢ x ∷ B
              → Γ ⊢ t ⇒* t′ ∷ A ∪ B
              → InjectionR t′ x
              → Γ ⊢ cases t u v ⇒* v ∘ x ∷ C
cases-subst*ᵣ ⊢A ⊢B ⊢C ⊢u ⊢v ⊢x t⇒t′ injrₙ =
  cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′
  ⇨∷* (∪-β₂ ⊢A ⊢B ⊢C ⊢x ⊢u ⊢v
       ⇨ id (▹▹∘ⱼ ⊢v ⊢x))

{--
substS▹▹ : ∀ {Γ : Con Term n} {F G t l}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([FG] : Γ ⊩ᵛ⟨ l ⟩ F ▹▹ G / [Γ])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
         → Γ ⊩ᵛ⟨ l ⟩ G / [Γ]
substS▹▹ {Γ = Γ} {F = F} {G} {t} {l} [Γ] [F] [FG] [t] =
  PE.subst (λ x → Γ ⊩ᵛ⟨ l ⟩ x / [Γ]) (wk1-sgSubst G t)
           (substSΠ {_} {Γ} {F} {wk1 G} {t} BΠ [Γ] [F] [FG] [t])
--}

{--
▹▹appᵛ : ∀ {Γ : Con Term n} {F G t u l}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
         ([FG] : Γ ⊩ᵛ⟨ l ⟩ F ▹▹ G / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F ▹▹ G / [Γ] / [FG])
         ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
       → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G / [Γ] / substS▹▹ {F = F} {G} {u} [Γ] [F] [FG] [u]
▹▹appᵛ {Γ = Γ} {F = F} {G} {t} {u} {l} [Γ] [F] [FG] [t] [u] =
  {!PE.subst (λ x → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ x / [Γ] / substS▹▹ {F = F} {G} {u} [Γ] [F] [FG] [u]) (wk1-sgSubst G t)!}
--}

appTermNd : ∀ {Γ : Con Term n} {F G t u l l′ l″}
            ([F] : Γ ⊩⟨ l″ ⟩ F)
            ([G] : Γ ⊩⟨ l′ ⟩ G)
            ([FG] : Γ ⊩⟨ l ⟩ F ▹▹ G)
            ([t] : Γ ⊩⟨ l ⟩ t ∷ F ▹▹ G / [FG])
            ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F / [F])
          → Γ ⊩⟨ l′ ⟩ t ∘ u ∷ G / [G]
appTermNd {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {l} {l′} {l″} [F] [G] [FG] [t] [u] =
  irrelevanceTerm′ (wk1-sgSubst G u)
                   (PE.subst (λ x → Γ ⊩⟨ l′ ⟩ x) (PE.sym (wk1-sgSubst G u)) [G])
                   [G]
                   (appTerm [F]
                            (PE.subst (λ x → Γ ⊩⟨ l′ ⟩ x) (PE.sym (wk1-sgSubst G u)) [G])
                            [FG] [t] [u])

app-congTermNd : ∀ {Γ : Con Term n} {F G t t′ u u′ l l′ l″}
                 ([F] : Γ ⊩⟨ l″ ⟩ F)
                 ([G] : Γ ⊩⟨ l′ ⟩ G)
                 ([FG] : Γ ⊩⟨ l ⟩ F ▹▹ G)
                 ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ F ▹▹ G / [FG])
                 ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F / [F])
                 ([u′] : Γ ⊩⟨ l″ ⟩ u′ ∷ F / [F])
                 ([u≡u′] : Γ ⊩⟨ l″ ⟩ u ≡ u′ ∷ F / [F])
                 → Γ ⊩⟨ l′ ⟩ t ∘ u ≡ t′ ∘ u′ ∷ G / [G]
app-congTermNd {Γ = Γ} {F = F} {G = G} {t = t} {t′ = t′} {u = u} {u′ = u′} {l} {l′} [F] [G] [FG] [t≡t′] [u] [u′] [u≡u′] =
  irrelevanceEqTerm′
    (wk1-sgSubst G u)
    (PE.subst (λ x → Γ ⊩⟨ l′ ⟩ x) (PE.sym (wk1-sgSubst G u)) [G])
    [G]
    (app-congTerm
      [F]
      (PE.subst (λ x → Γ ⊩⟨ l′ ⟩ x) (PE.sym (wk1-sgSubst G u)) [G])
      [FG] [t≡t′] [u] [u′] [u≡u′])


-- Reducibility of cases with a specific typing derivation
cases′ : ∀ {A B C t u v l l′}
         ([C] : Γ ⊩⟨ l ⟩ C)
         ([∪AB] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
         ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
         ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
         ([t] : Γ ⊩⟨ l′ ⟩ t ∷ A ∪ B / ∪-intr [∪AB])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
         ([v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
       → Γ ⊩⟨ l ⟩ cases t u v ∷ C / [C]
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C]
       (noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
       [▹▹AC] [▹▹BC] (∪₁ₜ p d ep pa i x) [u] [v]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  proj₁ (redSubst*Term
          (cases-subst*ₗ
            ⊢A ⊢B
            (escape [C])
            (escapeTerm (▹▹-intr [▹▹AC]) [u])
            (escapeTerm (▹▹-intr [▹▹BC]) [v])
            (escapeTerm (irrelevance′ (wk-id A) ([A'] id (wf ⊢A))) [pa])
            (redₜ d) i)
          [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) [u] [pa]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ A / [A]
  [pa] = irrelevanceTerm′ (wk-id A) ([A'] id (wf ⊢A)) [A] x
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C]
       (noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
       [▹▹AC] [▹▹BC] (∪₂ₜ p d ep pa i x) [u] [v]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  proj₁ (redSubst*Term
          (cases-subst*ᵣ
            ⊢A ⊢B
            (escape [C])
            (escapeTerm (▹▹-intr [▹▹AC]) [u])
            (escapeTerm (▹▹-intr [▹▹BC]) [v])
            (escapeTerm (irrelevance′ (wk-id B) ([B'] id (wf ⊢B))) [pa])
            (redₜ d) i)
          [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) [v] [pa]))
  where
  [B] : Γ ⊩⟨ l′ ⟩ B
  [B] = irrelevance′ (wk-id B) ([B'] id (wf ⊢B))

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ B / [B]
  [pa] = irrelevanceTerm′ (wk-id B) ([B'] id (wf ⊢B)) [B] x
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C]
       (noemb (∪ᵣ A' B' [ ⊢AB , ⊢AB' , D ] ⊢A' ⊢B' A≡A [A'] [B']))
       [▹▹AC] [▹▹BC] (∪₃ₜ p [ ⊢t , ⊢p , d ] ep (neNfₜ neK ⊢k k≡k)) [u] [v] =
  proj₁ (redSubst*Term redc [C] vc)
  where
  ⊢∪≡ : Γ ⊢ A ∪ B ≡ A' ∪ B'
  ⊢∪≡ = subset* D

  ∪≡ : A ∪ B PE.≡ A' ∪ B'
  ∪≡ = whnfRed* D ∪ₙ

  ⊢A : Γ ⊢ A
  ⊢A = PE.subst (λ x → Γ ⊢ x) (PE.sym (proj₁ (∪-PE-injectivity ∪≡))) ⊢A'

  ⊢B : Γ ⊢ B
  ⊢B = PE.subst (λ x → Γ ⊢ x) (PE.sym (proj₂ (∪-PE-injectivity ∪≡))) ⊢B'

  ⊢C : Γ ⊢ C
  ⊢C = escape [C]

  redc : Γ ⊢ cases t u v ⇒* cases p u v ∷ C
  redc = cases-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u]) (escapeTerm (▹▹-intr [▹▹BC]) [v]) (conv* d (sym ⊢∪≡))

  nc : Neutral (cases p u v)
  nc = casesₙ neK

  ⊢c : Γ ⊢ cases p u v ∷ C
  ⊢c = redSecond*Term redc

  vc : Γ ⊩⟨ l ⟩ cases p u v ∷ C / [C]
  vc = neuTerm [C] nc ⊢c (~-cases ⊢A ⊢B ⊢C (~-conv k≡k (sym ⊢∪≡))
                                  (escapeTermEq (▹▹-intr [▹▹AC]) (reflEqTerm (▹▹-intr [▹▹AC]) [u]))
                                  (escapeTermEq (▹▹-intr [▹▹BC]) (reflEqTerm (▹▹-intr [▹▹BC]) [v])))
cases′ {Γ = Γ} {t = t} {u = u} {v = v} {l = l} [C] (emb 0<1 (noemb (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T]))) [▹▹AC] [▹▹BC] [t] [u] [v] =
  cases′ [C] (noemb (∪ᵣ S T D ⊢S ⊢T A≡A [S] [T])) [▹▹AC] [▹▹BC] [t] [u] [v]

cases″ : ∀ {A B C t u v l l′}
         ([C] : Γ ⊩⟨ l ⟩ C)
         ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
         ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
         ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
         ([t] : Γ ⊩⟨ l′ ⟩ t ∷ A ∪ B / [∪AB])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / [▹▹AC])
         ([v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / [▹▹BC])
       → Γ ⊩⟨ l ⟩ cases t u v ∷ C / [C]
cases″ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C] [∪AB] [▹▹AC] [▹▹BC] [t] [u] [v] =
  cases′ [C] (∪-elim [∪AB]) (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC])
         (irrelevanceTerm [∪AB] (∪-intr (∪-elim [∪AB])) [t])
         (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
         (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

⊩neNfₗ : ∀ {n : Nat} {Γ : Con Term n} {A k k′ : Term n}
       → Γ ⊢ k ∷ A
       → Γ ⊩neNf k ≡ k′ ∷ A
       → Γ ⊩neNf k ∷ A
⊩neNfₗ {n} {Γ} {A} {k} {k′} h (neNfₜ₌ neK neM k≡m) = neNfₜ neK h (~-trans k≡m (~-sym k≡m))

[Natural]-propₗ : ∀ {n : Nat} {Γ : Con Term n} {k k′ : Term n}
                → Γ ⊢ k ∷ ℕ
                → [Natural]-prop Γ k k′
                → Natural-prop Γ k
[Natural]-propₗ {n} {Γ} {k} {.(suc _)} h (sucᵣ (ℕₜ₌ k₁ k₂ [ ⊢₁ , ⊢₂ , d ] d′ k≡k′ prop)) =
  sucᵣ (ℕₜ _ [ ⊢₁ , ⊢₂ , d ] (≅ₜ-trans k≡k′ (≅ₜ-sym k≡k′)) ([Natural]-propₗ ⊢₂ prop))
[Natural]-propₗ {n} {Γ} {k} {.zero} h zeroᵣ = zeroᵣ
[Natural]-propₗ {n} {Γ} {k} {k'} h (ne x) = ne (⊩neNfₗ h x)

[Empty]-propₗ : ∀ {n : Nat} {Γ : Con Term n} {k k′ : Term n}
              → Γ ⊢ k ∷ Empty
              → [Empty]-prop Γ k k′
              → Empty-prop Γ k
[Empty]-propₗ {n} {Γ} {k} {k′} ⊢k (ne (neNfₜ₌ neK neM k≡m)) =
  ne (neNfₜ neK ⊢k (~-trans k≡m (~-sym k≡m)))

-- move to where it belongs
⊩ₗ : ∀ {Γ : Con Term n} {A a b l}
     ([A] : Γ ⊩⟨ l ⟩ A)
   → Γ ⊩⟨ l ⟩ a ≡ b ∷ A / [A]
   → Γ ⊩⟨ l ⟩ a ∷ A / [A]
⊩ₗ {Γ = Γ} {A = .U} {a = a} {b = b} {l} (Uᵣ x) (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  Uₜ A d typeA (≅ₜ-trans A≡B (≅ₜ-sym A≡B)) [t]
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (ℕᵣ x) (ℕₜ₌ k k′ [ ⊢₁ , ⊢₂ , d ] d′ k≡k′ prop) =
  ℕₜ k [ ⊢₁ , ⊢₂ , d ] (≅ₜ-trans k≡k′ (≅ₜ-sym k≡k′)) ([Natural]-propₗ ⊢₂ prop)
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (Emptyᵣ x) (Emptyₜ₌ k k′ [ ⊢₁ , ⊢₂ , d ] d′ k≡k′ prop) =
  Emptyₜ k [ ⊢₁ , ⊢₂ , d ] (≅ₜ-trans k≡k′ (≅ₜ-sym k≡k′)) ([Empty]-propₗ ⊢₂ prop)
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (Unitᵣ [ ⊢A , ⊢B , D ]) (Unitₜ₌ k k′ d d′ k≡k′ (prop , prop₁)) =
  Unitₜ k d (≅ₜ-trans k≡k′ (≅ₜ-sym k≡k′)) prop
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (ne′ K D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ neK₁ neM k≡m)) =
  neₜ k d (neNfₜ neK₁ (⊢u-redₜ d) (~-trans k≡m (~-sym k≡m)))
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                       (Πₜ₌ f g d d' funcF funcG f≡g [f] [g] [f≡g]) = [f]
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                       (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) = [t]
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (∪ᵣ′ S T D ⊢S ⊢T A≡A [S] [T]) (p , r , c , d , p≅r , e , f , x) = e
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {¹} (emb {_} {.⁰} 0<1 [A]) h = ⊩ₗ [A] h

-- move to where it belongs
⊩ᵣ : ∀ {Γ : Con Term n} {A a b l}
     ([A] : Γ ⊩⟨ l ⟩ A)
   → Γ ⊩⟨ l ⟩ a ≡ b ∷ A / [A]
   → Γ ⊩⟨ l ⟩ b ∷ A / [A]
⊩ᵣ {Γ = Γ} {A = A} {a = a} {b = b} {l} [A] h =
  ⊩ₗ [A] (symEqTerm [A] h)

cases-cong′ : ∀ {A B C t t′ u u′ v v′ l l′}
            ([C] : Γ ⊩⟨ l ⟩ C)
            ([∪AB] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ A ∪ B / ∪-intr [∪AB])
            ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v≡v'] : Γ ⊩⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases t u v ≡ cases t′ u′ v′ ∷ C / [C]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₁ₜ₌ p p′ d d′ p≅p′ (q , e , q≅q′ , z) f pa pa′ i j x) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm [C] [casest≡casesp] (transEqTerm [C] [u∘pa≡] (symEqTerm [C] [casest′≡casesp′]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  ⊩u : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  ⊩u = ⊩ₗ (▹▹-intr [▹▹AC]) [u≡u′]

  ⊩v : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  ⊩v = ⊩ₗ (▹▹-intr [▹▹BC]) [v≡v′]

  ⊩u′ : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  ⊩u′ = ⊩ᵣ (▹▹-intr [▹▹AC]) [u≡u′]

  ⊩v′ : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  ⊩v′ = ⊩ᵣ (▹▹-intr [▹▹BC]) [v≡v′]

  [pa≡pa′] : Γ ⊩⟨ l′ ⟩ pa ≡ pa′ ∷ A / [A]
  [pa≡pa′] = irrelevanceEqTerm′ (wk-id A) ([A'] id (wf ⊢A)) [A] x

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ A / [A]
  [pa] = ⊩ₗ [A] [pa≡pa′]

  [pa′] : Γ ⊩⟨ l′ ⟩ pa′ ∷ A / [A]
  [pa′] = ⊩ᵣ [A] [pa≡pa′]

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases t u v ≡ u ∘ pa ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term (cases-subst*ₗ ⊢A ⊢B (escape [C])
                                                        (escapeTerm (▹▹-intr [▹▹AC]) ⊩u)
                                                        (escapeTerm (▹▹-intr [▹▹BC]) ⊩v)
                                                        (escapeTerm [A] [pa])
                                                        (redₜ d) i)
                                          [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) ⊩u [pa]))
  [casest′≡casesp′] : Γ ⊩⟨ l ⟩ cases t′ u′ v′ ≡ u′ ∘ pa′ ∷ C / [C]
  [casest′≡casesp′] = proj₂ (redSubst*Term (cases-subst*ₗ ⊢A ⊢B (escape [C])
                                                          (escapeTerm (▹▹-intr [▹▹AC]) ⊩u′)
                                                          (escapeTerm (▹▹-intr [▹▹BC]) ⊩v′)
                                                          (escapeTerm [A] [pa′])
                                                          (redₜ d′) j)
                                           [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) ⊩u′ [pa′]))

  [u∘pa≡] : Γ ⊩⟨ l ⟩ u ∘ pa ≡ u′ ∘ pa′ ∷ C / [C]
  [u∘pa≡] = app-congTermNd [A] [C] (▹▹-intr [▹▹AC]) [u≡u′] [pa] [pa′] [pa≡pa′]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₂ₜ₌ p p′ d d′ p≅p′ e f pa pa′ i j x) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm [C] [casest≡casesp] (transEqTerm [C] [v∘pa≡] (symEqTerm [C] [casest′≡casesp′]))
  where
  [B] : Γ ⊩⟨ l′ ⟩ B
  [B] = irrelevance′ (wk-id B) ([B'] id (wf ⊢B))

  ⊩u : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  ⊩u = ⊩ₗ (▹▹-intr [▹▹AC]) [u≡u′]

  ⊩v : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  ⊩v = ⊩ₗ (▹▹-intr [▹▹BC]) [v≡v′]

  ⊩u′ : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  ⊩u′ = ⊩ᵣ (▹▹-intr [▹▹AC]) [u≡u′]

  ⊩v′ : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  ⊩v′ = ⊩ᵣ (▹▹-intr [▹▹BC]) [v≡v′]

  [pa≡pa′] : Γ ⊩⟨ l′ ⟩ pa ≡ pa′ ∷ B / [B]
  [pa≡pa′] = irrelevanceEqTerm′ (wk-id B) ([B'] id (wf ⊢B)) [B] x

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ B / [B]
  [pa] = ⊩ₗ [B] [pa≡pa′]

  [pa′] : Γ ⊩⟨ l′ ⟩ pa′ ∷ B / [B]
  [pa′] = ⊩ᵣ [B] [pa≡pa′]

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases t u v ≡ v ∘ pa ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term (cases-subst*ᵣ ⊢A ⊢B (escape [C])
                                                        (escapeTerm (▹▹-intr [▹▹AC]) ⊩u)
                                                        (escapeTerm (▹▹-intr [▹▹BC]) ⊩v)
                                                        (escapeTerm [B] [pa])
                                                        (redₜ d) i)
                                          [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) ⊩v [pa]))
  [casest′≡casesp′] : Γ ⊩⟨ l ⟩ cases t′ u′ v′ ≡ v′ ∘ pa′ ∷ C / [C]
  [casest′≡casesp′] = proj₂ (redSubst*Term (cases-subst*ᵣ ⊢A ⊢B (escape [C])
                                                          (escapeTerm (▹▹-intr [▹▹AC]) ⊩u′)
                                                          (escapeTerm (▹▹-intr [▹▹BC]) ⊩v′)
                                                          (escapeTerm [B] [pa′])
                                                          (redₜ d′) j)
                                           [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) ⊩v′ [pa′]))

  [v∘pa≡] : Γ ⊩⟨ l ⟩ v ∘ pa ≡ v′ ∘ pa′ ∷ C / [C]
  [v∘pa≡] = app-congTermNd [B] [C] (▹▹-intr [▹▹BC]) [v≡v′] [pa] [pa′] [pa≡pa′]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₃ₜ₌ p p′ d d′ p≅p′ e f (neNfₜ₌ neK neK′ k≡k)) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm [C] [casest≡casesp] (transEqTerm [C] [casesp≡casesp′] (symEqTerm [C] [casest′≡casesp′]))
  where
  [u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u] = ⊩ₗ (▹▹-intr [▹▹AC]) [u≡u′]

  [v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v] = ⊩ₗ (▹▹-intr [▹▹BC]) [v≡v′]

  [u′] : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u′] = ⊩ᵣ (▹▹-intr [▹▹AC]) [u≡u′]

  [v′] : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v′] = ⊩ᵣ (▹▹-intr [▹▹BC]) [v≡v′]

  nc : Neutral (cases p u v)
  nc = casesₙ neK

  nc′ : Neutral (cases p′ u′ v′)
  nc′ = casesₙ neK′

  ⊢C : Γ ⊢ C
  ⊢C = escape [C]

  redc : Γ ⊢ cases t u v ⇒* cases p u v ∷ C
  redc = cases-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u]) (escapeTerm (▹▹-intr [▹▹BC]) [v]) (redₜ d)

  redc′ : Γ ⊢ cases t′ u′ v′ ⇒* cases p′ u′ v′ ∷ C
  redc′ = cases-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u′]) (escapeTerm (▹▹-intr [▹▹BC]) [v′]) (redₜ d′)

  ⊢c : Γ ⊢ cases p u v ∷ C
  ⊢c = redSecond*Term redc

  ⊢c′ : Γ ⊢ cases p′ u′ v′ ∷ C
  ⊢c′ = redSecond*Term redc′

  vc : Γ ⊩⟨ l ⟩ cases p u v ∷ C / [C]
  vc = neuTerm [C] nc ⊢c (~-cases ⊢A ⊢B ⊢C (~-trans k≡k (~-sym k≡k))
                                  (escapeTermEq (▹▹-intr [▹▹AC]) (reflEqTerm (▹▹-intr [▹▹AC]) [u]))
                                  (escapeTermEq (▹▹-intr [▹▹BC]) (reflEqTerm (▹▹-intr [▹▹BC]) [v])))

  vc′ : Γ ⊩⟨ l ⟩ cases p′ u′ v′ ∷ C / [C]
  vc′ = neuTerm [C] nc′ ⊢c′ (~-cases ⊢A ⊢B ⊢C (~-trans (~-sym k≡k) k≡k)
                                  (escapeTermEq (▹▹-intr [▹▹AC]) (reflEqTerm (▹▹-intr [▹▹AC]) [u′]))
                                  (escapeTermEq (▹▹-intr [▹▹BC]) (reflEqTerm (▹▹-intr [▹▹BC]) [v′])))

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases t u v ≡ cases p u v ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term redc [C] vc)

  [casest′≡casesp′] : Γ ⊩⟨ l ⟩ cases t′ u′ v′ ≡ cases p′ u′ v′ ∷ C / [C]
  [casest′≡casesp′] = proj₂ (redSubst*Term redc′ [C] vc′)

  [casesp≡casesp′] : Γ ⊩⟨ l ⟩ cases p u v ≡ cases p′ u′ v′ ∷ C / [C]
  [casesp≡casesp′] = neuEqTerm [C] nc nc′ ⊢c ⊢c′
                       (~-cases ⊢A ⊢B ⊢C k≡k (escapeTermEq (▹▹-intr [▹▹AC]) [u≡u′])
                                             (escapeTermEq (▹▹-intr [▹▹BC]) [v≡v′]))
cases-cong′ [C] (emb 0<1 x) [▹▹AC] [▹▹BC] [t≡t′] [u≡u′] [v≡v′] =
  cases-cong′ [C] x [▹▹AC] [▹▹BC] [t≡t′] [u≡u′] [v≡v′]

cases-cong″ : ∀ {A B C t t′ u u′ v v′ l l′}
            ([C] : Γ ⊩⟨ l ⟩ C)
            ([∪AB] : Γ ⊩⟨ l′ ⟩ A ∪ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ A ∪ B / [∪AB])
            ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [▹▹AC])
            ([v≡v'] : Γ ⊩⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases t u v ≡ cases t′ u′ v′ ∷ C / [C]
cases-cong″ {Γ = Γ} {A = A} {B = B} {C = C} {t} {t′} {u} {u′} {v} {v′} {l} {l′}
            [C] [∪AB] [▹▹AC] [▹▹BC] [t≡t′]
            [u≡u′] [v≡v′] =
  cases-cong′ [C] (∪-elim [∪AB]) (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC])
              (irrelevanceEqTerm [∪AB] (∪-intr (∪-elim [∪AB])) [t≡t′])
              (irrelevanceEqTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u≡u′])
              (irrelevanceEqTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v≡v′])

subst▹▹ : {m n : Nat} (σ : Subst m n) (a b : Term n)
        → subst σ (a ▹▹ b)
        PE.≡ subst σ a ▹▹ subst σ b
subst▹▹ {m} {n} σ a b =
  PE.cong₂ (λ x y → Π x ▹ y)
           PE.refl
           (PE.trans (subst-wk b) (PE.sym (wk-subst b)))

-- Validity of cases
casesᵛ : ∀ {Γ : Con Term n} {A B C t u v l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
         ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
         ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
         → Γ ⊩ᵛ⟨ l ⟩ cases t u v ∷ C / [Γ] / [C]
casesᵛ {Γ = Γ} {A} {B} {C} {t} {u} {v} {l} [Γ] [A] [B] [C] [t] [u] [v] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB]  = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      σcases : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → Δ ⊩⟨ l ⟩ subst σ (cases t u v) ∷ subst σ C / proj₁ ([C] ⊢Δ [σ])
      σcases {Δ} {σ} ⊢Δ [σ] =
        let ⊩σC    = proj₁ ([C] ⊢Δ [σ])
            ⊩σ∪AB  = proj₁ ([∪AB] ⊢Δ [σ])
            ⊩σ▹▹AC = proj₁ ([▹▹AC] ⊢Δ [σ])
            ⊩σ▹▹BC = proj₁ ([▹▹BC] ⊢Δ [σ])
            ⊩σt    = proj₁ ([t] ⊢Δ [σ])
            ⊩σu    = proj₁ ([u] ⊢Δ [σ])
            ⊩σv    = proj₁ ([v] ⊢Δ [σ])
        in cases″ ⊩σC ⊩σ∪AB
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
  in  σcases ⊢Δ [σ] ,
      λ {σ′} [σ′] [σ≡σ′] →
        let [σC]     = proj₁ ([C] ⊢Δ [σ])
            [σ∪AB]   = proj₁ ([∪AB] ⊢Δ [σ])
            [σ▹▹AC]  = proj₁ ([▹▹AC] ⊢Δ [σ])
            [σ▹▹BC]  = proj₁ ([▹▹BC] ⊢Δ [σ])
            [σt]     = proj₁ ([t] ⊢Δ [σ])
            [σt≡t′]  = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σu≡u′]  = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σv≡v′]  = proj₂ ([v] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  cases-cong″ [σC] [σ∪AB]
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

cases-congᵛ : ∀ {Γ : Con Term n} {A B C t t′ u u′ v v′ l}
              ([Γ]    : ⊩ᵛ Γ)
              ([A]    : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([B]    : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
              ([C]    : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
              ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
              ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
              ([v≡v'] : Γ ⊩ᵛ⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ cases t u v ≡ cases t′ u′ v′ ∷ C / [Γ] / [C]
cases-congᵛ {Γ = Γ} {A} {B} {C} {t} {t′} {u} {u′} {v} {v′} {l} [Γ] [A] [B] [C] [t≡t′] [u≡u′] [v≡v'] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  {!!}
{--
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
  in  fst-cong″ ⊩σF ⊩σΣFG ⊩σt≡t′
--}
