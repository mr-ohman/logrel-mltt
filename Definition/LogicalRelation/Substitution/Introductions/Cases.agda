{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

open import Definition.Typed.EqualityRelation


module Definition.LogicalRelation.Substitution.Introductions.Cases {{eqrel : EqRelSet}} where
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
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {l} (∥ᵣ′ S D ⊢S A≡A [S]) (p , r , c , d , p≅r , e , f , x) = e
⊩ₗ {Γ = Γ} {A = A} {a = a} {b = b} {¹} (emb {_} {.⁰} 0<1 [A]) h = ⊩ₗ [A] h

-- move to where it belongs
⊩ᵣ : ∀ {Γ : Con Term n} {A a b l}
     ([A] : Γ ⊩⟨ l ⟩ A)
   → Γ ⊩⟨ l ⟩ a ≡ b ∷ A / [A]
   → Γ ⊩⟨ l ⟩ b ∷ A / [A]
⊩ᵣ {Γ = Γ} {A = A} {a = a} {b = b} {l} [A] h =
  ⊩ₗ [A] (symEqTerm [A] h)

redSecond*Term : ∀ {A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ∷ A
redSecond*Term (id t) = t
redSecond*Term (t⇒t′ ⇨ t′⇒*u) = redSecond*Term t′⇒*u

▹▹∘ⱼ : ∀ {g a F G}
     → Γ ⊢     g ∷ F ▹▹ G
     → Γ ⊢     a ∷ F
     → Γ ⊢ g ∘ a ∷ G
▹▹∘ⱼ {l} {Γ} {g} {a} {F} {G} ⊢g ⊢a =
  PE.subst (λ x → Γ ⊢ g ∘ a ∷ x)
           (wk1-sgSubst G a)
           (⊢g ∘ⱼ ⊢a)

cases-subst* : ∀ {A B C t t′ u v}
             → Γ ⊢ A
             → Γ ⊢ B
             → Γ ⊢ C
             → Γ ⊢ u ∷ A ▹▹ C
             → Γ ⊢ v ∷ B ▹▹ C
             → Γ ⊢ t ⇒* t′ ∷ A ∪ B
             → Γ ⊢ cases C t u v ⇒* cases C t′ u v ∷ C
cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v (id x) = id (casesⱼ x ⊢u ⊢v ⊢C)
cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v (x ⇨ t⇒t′) = cases-subst ⊢A ⊢B ⊢C ⊢u ⊢v x ⇨ cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′

cases-subst*ₗ : ∀ {A B C t t′ u v x}
              → Γ ⊢ A
              → Γ ⊢ B
              → Γ ⊢ C
              → Γ ⊢ u ∷ A ▹▹ C
              → Γ ⊢ v ∷ B ▹▹ C
              → Γ ⊢ x ∷ A
              → Γ ⊢ t ⇒* t′ ∷ A ∪ B
              → InjectionL t′ x
              → Γ ⊢ cases C t u v ⇒* u ∘ x ∷ C
cases-subst*ₗ ⊢A ⊢B ⊢C ⊢u ⊢v ⊢x t⇒t′ injlₙ =
  cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′
  ⇨∷* (∪-β₁ ⊢B ⊢C ⊢x ⊢u ⊢v
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
              → Γ ⊢ cases C t u v ⇒* v ∘ x ∷ C
cases-subst*ᵣ ⊢A ⊢B ⊢C ⊢u ⊢v ⊢x t⇒t′ injrₙ =
  cases-subst* ⊢A ⊢B ⊢C ⊢u ⊢v t⇒t′
  ⇨∷* (∪-β₂ ⊢A ⊢C ⊢x ⊢u ⊢v
       ⇨ id (▹▹∘ⱼ ⊢v ⊢x))

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

substS▹▹ : ∀ {Γ : Con Term n} {F G t l}
           ([Γ]  : ⊩ᵛ Γ)
           ([F]  : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([FG] : Γ ⊩ᵛ⟨ l ⟩ F ▹▹ G / [Γ])
           ([t]  : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
         → Γ ⊩ᵛ⟨ l ⟩ G / [Γ]
substS▹▹ {Γ = Γ} {F = F} {G} {t} {l} [Γ] [F] [FG] [t] =
  PE.subst (λ x → Γ ⊩ᵛ⟨ l ⟩ x / [Γ]) (wk1-sgSubst G t)
           (substSΠ {_} {Γ} {F} {wk1 G} {t} BΠ [Γ] [F] [FG] [t])

subst▹▹ : {m n : Nat} (σ : Subst m n) (a b : Term n)
        → subst σ (a ▹▹ b)
        PE.≡ subst σ a ▹▹ subst σ b
subst▹▹ {m} {n} σ a b =
  PE.cong₂ (λ x y → Π x ▹ y)
           PE.refl
           (PE.trans (subst-wk b) (PE.sym (wk-subst b)))

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

▹▹appᵛ : ∀ {Γ : Con Term n} {F G t u l}
         ([Γ]  : ⊩ᵛ Γ)
         ([F]  : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
         ([G]  : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
         ([FG] : Γ ⊩ᵛ⟨ l ⟩ F ▹▹ G / [Γ])
         ([t]  : Γ ⊩ᵛ⟨ l ⟩ t ∷ F ▹▹ G / [Γ] / [FG])
         ([u]  : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
       → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G / [Γ] / [G]
▹▹appᵛ {Γ = Γ} {F = F} {G} {t} {u} {l} [Γ] [F] [G] [FG] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σF]    = proj₁ ([F] ⊢Δ [σ])
      [σG]    = proj₁ ([G] ⊢Δ [σ])
      [σFG]   = proj₁ ([FG] ⊢Δ [σ])
      [σF▹▹G] = irrelevance′ (subst▹▹ σ F G) [σFG]
      [σt]    = proj₁ ([t] ⊢Δ [σ])
      [σu]    = proj₁ ([u] ⊢Δ [σ])
  in appTermNd [σF] [σG] [σF▹▹G]
               (irrelevanceTerm′ (subst▹▹ σ F G) [σFG] [σF▹▹G] [σt])
               [σu] ,
     λ {σ′} [σ′] [σ≡σ′] →
       let [σu≡u′] = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
           [σt≡t′] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
       in app-congTermNd [σF] [σG] [σF▹▹G]
                         (irrelevanceEqTerm′ (subst▹▹ σ F G) [σFG] [σF▹▹G] [σt≡t′])
                         [σu] (⊩ᵣ [σF] [σu≡u′]) [σu≡u′]

-- Reducibility of cases with a specific typing derivation
cases′ : ∀ {A B C t u v l l′}
         ([C] : Γ ⊩⟨ l ⟩ C)
         ([∪AB] : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
         ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
         ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
         ([t] : Γ ⊩⟨ l′ ⟩ t ∷ A ∪ B / ∪-intr [∪AB])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
         ([v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
       → Γ ⊩⟨ l ⟩ cases C t u v ∷ C / [C]
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

  redc : Γ ⊢ cases C t u v ⇒* cases C p u v ∷ C
  redc = cases-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u]) (escapeTerm (▹▹-intr [▹▹BC]) [v]) (conv* d (sym ⊢∪≡))

  nc : Neutral (cases C p u v)
  nc = casesₙ neK

  ⊢c : Γ ⊢ cases C p u v ∷ C
  ⊢c = redSecond*Term redc

  vc : Γ ⊩⟨ l ⟩ cases C p u v ∷ C / [C]
  vc = neuTerm [C] nc ⊢c (~-cases ⊢A ⊢B (escapeEq [C] (reflEq [C]))(~-conv k≡k (sym ⊢∪≡))
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
       → Γ ⊩⟨ l ⟩ cases C t u v ∷ C / [C]
cases″ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C] [∪AB] [▹▹AC] [▹▹BC] [t] [u] [v] =
  cases′ [C] (∪-elim [∪AB]) (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC])
         (irrelevanceTerm [∪AB] (∪-intr (∪-elim [∪AB])) [t])
         (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
         (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

typedRed : ∀ {A B} → Γ ⊢ A ⇒* B → Γ ⊢ A
typedRed (id x) = x
typedRed (univ x ⇨ h) = univ (redFirstTerm x)

escapeTerm′ : ∀ {n} {Γ : Con Term n} {l A A′ t}
                ([A]    : Γ ⊩⟨ l ⟩ A)
                ([A′]   : Γ ⊩⟨ l ⟩ A′)
                ([A≡A′] : Γ ⊩⟨ l ⟩ A ≡ A′ / [A])
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A′
escapeTerm′ {n} {Γ} {l} {A = A} {A′ = A′} {t} [A] [A′] [A≡A′] h =
  escapeTerm [A′] h′
  where
  h′ : Γ ⊩⟨ l ⟩ t ∷ A′ / [A′]
  h′ = convTerm₁ [A] [A′] [A≡A′] h

≡⊩▹▹′ : ∀ {n} {Γ : Con Term n} {l A C C′}
          ([C′] : Γ ⊩⟨ l ⟩ C′)
       → Γ ⊩′⟨ l ⟩▹▹ (A ▹▹ C)
       → Γ ⊩′⟨ l ⟩▹▹ (A ▹▹ C′)
≡⊩▹▹′ {n} {Γ} {l} {A} {C} {C′} [C′] (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  with proj₁ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
     | proj₂ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
... | e | f =
  Bᵣ A (wk1 C′)
       (idRed:*: (Πⱼ ⊢A ▹ Wk.wk (step id) (⊢Γ ∙ ⊢A) ⊢C′))
       ⊢A
       (Wk.wk (step id) (⊢Γ ∙ ⊢A) ⊢C′)
       (≅-Π-cong ⊢A
                 (escapeEq [A]′ (reflEq [A]′))
                 (escapeEq (wk (step id) (⊢Γ ∙ ⊢A) [C′])
                           (reflEq (wk (step id) (⊢Γ ∙ ⊢A) [C′]))))
       [A] [C′]′ [C′]″
  where
  ⊢A : Γ ⊢ A
  ⊢A = PE.subst (λ x → Γ ⊢ x) (PE.sym e) ⊢F

  ⊢Γ : ⊢ Γ
  ⊢Γ = wf ⊢A

  [A] : {m : Nat} {ρ : Wk m n} {Δ : Con Term m}
      → ρ ∷ Δ ⊆ Γ → ⊢ Δ → Δ ⊩⟨ l ⟩ (U.wk ρ A)
  [A] rewrite e = [F]

  [A]′ : Γ ⊩⟨ l ⟩ A
  [A]′ = PE.subst (λ x → Γ ⊩⟨ l ⟩ x) (wk-id A) ([A] id (wf ⊢A))

  ⊢C′ : Γ ⊢ C′
  ⊢C′ = escape [C′]

  [C′]′ : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} {a : Term m}
          ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ A / [A] [ρ] ⊢Δ)
        → Δ ⊩⟨ l ⟩ U.wk (lift ρ) (wk1 C′) [ a ]
  [C′]′ {m = m} {ρ = ρ} {Δ = Δ} {a = a} [ρ] ⊢Δ [a]
    rewrite PE.sym (wk1-wk≡lift-wk1 ρ C′) | wk1-sgSubst (U.wk ρ C′) a
    = wk [ρ] ⊢Δ [C′]

  [C′]″ : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} {a b : Term m}
          ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ A / [A] [ρ] ⊢Δ)
        → Δ ⊩⟨ l ⟩ b ∷ U.wk ρ A / [A] [ρ] ⊢Δ
        → Δ ⊩⟨ l ⟩ a ≡ b ∷ U.wk ρ A / [A] [ρ] ⊢Δ
        → Δ ⊩⟨ l ⟩ U.wk (lift ρ) (wk1 C′) [ a ] ≡ U.wk (lift ρ) (wk1 C′) [ b ] / [C′]′ [ρ] ⊢Δ [a]
  [C′]″ {m = m} {ρ = ρ} {Δ = Δ} {a = a} {b = b} [ρ] ⊢Δ [a] ⊢b ⊢a≡b
    rewrite PE.sym (wk1-wk≡lift-wk1 ρ C′) | wk1-sgSubst (U.wk ρ C′) a | wk1-sgSubst (U.wk ρ C′) b
    = reflEq (wk [ρ] ⊢Δ [C′])

⊩′▹▹⁰¹ : ∀ {n} {Γ : Con Term n} {A B}
       → Γ ⊩′⟨ ⁰ ⟩▹▹ (A ▹▹ B)
       → Γ ⊩′⟨ ¹ ⟩▹▹ (A ▹▹ B)
⊩′▹▹⁰¹ {n} {Γ} {A} {B} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  with proj₁ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
     | proj₂ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
... | e | f rewrite PE.sym e | PE.sym f =
  Bᵣ A (U.wk1 B) D ⊢F ⊢G A≡A [A]′ [B]′ G-ext
  where
  [A]′ : {m : Nat} {ρ : Wk m n} {Δ : Con Term m}
     → ρ ∷ Δ ⊆ Γ → ⊢ Δ → Δ ⊩⟨ ¹ ⟩ (U.wk ρ A)
  [A]′ {m} {ρ} {Δ} [ρ] ⊢Δ = maybeEmb′ ([F] [ρ] ⊢Δ)

  [B]′ : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} {a : Term m}
         ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([a] : Δ ⊩⟨ ⁰ ⟩ a ∷ U.wk ρ A / [F] [ρ] ⊢Δ)
       → Δ ⊩⟨ ¹ ⟩ U.wk (lift ρ) (wk1 B) [ a ]
  [B]′ {m = m} {ρ = ρ} {Δ = Δ} {a = a} [ρ] ⊢Δ [a]
    = maybeEmb′ ([G] [ρ] ⊢Δ [a])

≡⊩▹▹ : ∀ {n} {Γ : Con Term n} {l A C C′}
         ([C′] : Γ ⊩⟨ l ⟩ C′)
       → Γ ⊩⟨ l ⟩▹▹ (A ▹▹ C)
       → Γ ⊩⟨ l ⟩▹▹ (A ▹▹ C′)
≡⊩▹▹ {n} {Γ} {l} {A} {C} {C′} [C′] (noemb x) =
  noemb (≡⊩▹▹′ [C′] x)
≡⊩▹▹ {n} {Γ} {.¹} {A} {C} {C′} [C′] (emb 0<1 (noemb x)) =
  noemb (≡⊩▹▹′ {n} {Γ} {¹} {A} {C} {C′} [C′] (⊩′▹▹⁰¹ x))

⊩▹▹-cong′ : ∀ {n} {Γ : Con Term n} {l l′ A C C′}
              ([A]    : Γ ⊩⟨ l′ ⟩ A)
              ([C]    : Γ ⊩⟨ l ⟩ C)
              ([C′]   : Γ ⊩⟨ l ⟩ C′)
              ([C≡C′] : Γ ⊩⟨ l ⟩ C ≡ C′ / [C])
              ([▹▹AC] : Γ ⊩′⟨ l ⟩▹▹ A ▹▹ C)
          → Γ ⊩⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / Bᵣ BΠ [▹▹AC]
⊩▹▹-cong′ {n = n} {Γ} {l} {l′} {A} {C} {C′} [A] [C] [C′] [C≡C′] (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  with proj₁ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
     | proj₂ (B-PE-injectivity BΠ (whnfRed* (red D) Πₙ))
... | e | f rewrite PE.sym e | PE.sym f =
  B₌ A (U.wk1 C′)
     (id ⊢A▹▹C′)
     (≅-Π-cong ⊢F ⊢A≅A (≅-wk (step id) (wf ⊢A▹▹C′ ∙ ⊢A) ⊢C≅C′))
     wk[A≡A]
     wk[C≡C′]
  where
  ⊢A : Γ ⊢ A
  ⊢A = escape [A]

  ⊢C : Γ ⊢ C
  ⊢C = escape [C]

  ⊢C′ : Γ ⊢ C′
  ⊢C′ = escape [C′]

  ⊢A▹▹C′ : Γ ⊢ A ▹▹ C′
  ⊢A▹▹C′ = ▹▹-intro ⊢A ⊢C′

  [A≡A] : Γ ⊩⟨ l′ ⟩ A ≡ A / [A]
  [A≡A] = reflEq [A]

  ⊢A≅A : Γ ⊢ A ≅ A
  ⊢A≅A = escapeEq [A] [A≡A]

  ⊢C≅C′ : Γ ⊢ C ≅ C′
  ⊢C≅C′ = escapeEq [C] [C≡C′]

  wk[A≡A] : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ A / [F] [ρ] ⊢Δ
  wk[A≡A] {m} {ρ} {Δ} [ρ] ⊢Δ = reflEq ([F] [ρ] ⊢Δ)

  wk[C≡C′] : {m : Nat} {ρ : Wk m n} {Δ : Con Term m} {a : Term m} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
             ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ A / [F] [ρ] ⊢Δ)
           → Δ ⊩⟨ l ⟩ U.wk (lift ρ) (U.wk (step id) C) [ a ] ≡ U.wk (lift ρ) (wk1 C′) [ a ] / [G] [ρ] ⊢Δ [a]
  wk[C≡C′] {m} {ρ} {Δ} {a} [ρ] ⊢Δ [a] = q ([G] [ρ] ⊢Δ [a])
    where
    q : ([X] : Δ ⊩⟨ l ⟩ U.wk (lift ρ) (U.wk (step id) C) [ a ])
      → Δ ⊩⟨ l ⟩ U.wk (lift ρ) (U.wk (step id) C) [ a ] ≡ U.wk (lift ρ) (wk1 C′) [ a ] / [X]
    q [X] rewrite PE.sym (wk1-wk≡lift-wk1 ρ C)
                | PE.sym (wk1-wk≡lift-wk1 ρ C′)
                | wk1-sgSubst (U.wk ρ C) a
                | wk1-sgSubst (U.wk ρ C′) a
      = irrelevanceEq (wk [ρ] ⊢Δ [C]) [X] (wkEq [ρ] ⊢Δ [C] [C≡C′])

⊩▹▹-cong : ∀ {n} {Γ : Con Term n} {l l′ A C C′}
              ([A]    : Γ ⊩⟨ l′ ⟩ A)
              ([C]    : Γ ⊩⟨ l ⟩ C)
              ([C′]   : Γ ⊩⟨ l ⟩ C′)
              ([C≡C′] : Γ ⊩⟨ l ⟩ C ≡ C′ / [C])
              ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
          → Γ ⊩⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / ▹▹-intr [▹▹AC]
⊩▹▹-cong {n = n} {Γ} {l} {l′} {A} {C} {C′} [A] [C] [C′] [C≡C′] (noemb x) =
  ⊩▹▹-cong′ [A] [C] [C′] [C≡C′] x
⊩▹▹-cong {n = n} {Γ} {.¹} {l′} {A} {C} {C′} [A] [C] [C′] [C≡C′] (emb 0<1 (noemb x)) =
  irrelevanceEq (Bᵣ BΠ (⊩′▹▹⁰¹ x)) (emb 0<1 (Bᵣ BΠ x)) (⊩▹▹-cong′ [A] [C] [C′] [C≡C′] (⊩′▹▹⁰¹ x))

▹▹-congᵛ′ : ∀ {n} {Γ : Con Term n} {l A C C′}
             ([Γ]     : ⊩ᵛ Γ)
             ([A]    : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([C]    : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
             ([C′]   : Γ ⊩ᵛ⟨ l ⟩ C′ / [Γ])
             ([C≡C′] : Γ ⊩ᵛ⟨ l ⟩ C ≡ C′ / [Γ] / [C])
           → Γ ⊩ᵛ⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
▹▹-congᵛ′ {n = n} {Γ} {l} {A} {C} {C′} [Γ] [A] [C] [C′] [C≡C′] =
  nd-congᵛ {F = A} {F′ = A} {G = C} {G′ = C′} BΠ [Γ] [A] [A] (reflᵛ {A = A} [Γ] [A]) [C] [C′] [C≡C′]

cases-cong′ : ∀ {A B C C′ t t′ u u′ v v′ l l′}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([C′]   : Γ ⊩⟨ l ⟩ C′)
            ([C≡C′] : Γ ⊩⟨ l ⟩ C ≡ C′ / [C])
            ([∪AB]  : Γ ⊩⟨ l′ ⟩∪ A ∪ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ A ∪ B / ∪-intr [∪AB])
            ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v≡v′] : Γ ⊩⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C t u v ≡ cases C′ t′ u′ v′ ∷ C / [C]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C] [C′] [C≡C′]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₁ₜ₌ p p′ d d′ p≅p′ (q , e , q≅q′ , z) f pa pa′ i j x) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm
    [C]
    [casest≡casesp]
    (transEqTerm [C] [u∘pa≡] (symEqTerm [C] [casest′≡casesp″]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

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

  [pa≡pa′] : Γ ⊩⟨ l′ ⟩ pa ≡ pa′ ∷ A / [A]
  [pa≡pa′] = irrelevanceEqTerm′ (wk-id A) ([A'] id (wf ⊢A)) [A] x

  [pa] : Γ ⊩⟨ l′ ⟩ pa ∷ A / [A]
  [pa] = ⊩ₗ [A] [pa≡pa′]

  [pa′] : Γ ⊩⟨ l′ ⟩ pa′ ∷ A / [A]
  [pa′] = ⊩ᵣ [A] [pa≡pa′]

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases C t u v ≡ u ∘ pa ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term (cases-subst*ₗ ⊢A ⊢B (escape [C])
                                                        (escapeTerm (▹▹-intr [▹▹AC]) ⊩u)
                                                        (escapeTerm (▹▹-intr [▹▹BC]) ⊩v)
                                                        (escapeTerm [A] [pa])
                                                        (redₜ d) i)
                                          [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) ⊩u [pa]))

  [▹▹AC′] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C′
  [▹▹AC′] = ≡⊩▹▹ {Γ = Γ} {l} {A} {C} {C′} [C′] [▹▹AC]

  [▹▹BC′] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C′
  [▹▹BC′] = ≡⊩▹▹ {Γ = Γ} {l} {B} {C} {C′} [C′] [▹▹BC]

  [▹▹AC≡′] : Γ ⊩⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / ▹▹-intr [▹▹AC]
  [▹▹AC≡′] = ⊩▹▹-cong [A] [C] [C′] [C≡C′] [▹▹AC]

  [▹▹BC≡′] : Γ ⊩⟨ l ⟩ B ▹▹ C ≡ B ▹▹ C′ / ▹▹-intr [▹▹BC]
  [▹▹BC≡′] = ⊩▹▹-cong [B] [C] [C′] [C≡C′] [▹▹BC]

  ⊩u″ : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C′ / ▹▹-intr [▹▹AC′]
  ⊩u″ = convTerm₁ (▹▹-intr [▹▹AC]) (▹▹-intr [▹▹AC′]) [▹▹AC≡′] ⊩u′

  ⊩v″ : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C′ / ▹▹-intr [▹▹BC′]
  ⊩v″ = convTerm₁ (▹▹-intr [▹▹BC]) (▹▹-intr [▹▹BC′]) [▹▹BC≡′] ⊩v′

  ⊢casest′ : Γ ⊢ cases C′ t′ u′ v′ ⇒* u′ ∘ pa′ ∷ C′
  ⊢casest′ = cases-subst*ₗ ⊢A ⊢B (escape [C′])
                                 (escapeTerm (▹▹-intr [▹▹AC′]) ⊩u″)
                                 (escapeTerm (▹▹-intr [▹▹BC′]) ⊩v″)
                                 (escapeTerm [A] [pa′])
                                 (redₜ d′) j

  [casest′≡casesp″] : Γ ⊩⟨ l ⟩ cases C′ t′ u′ v′ ≡ u′ ∘ pa′ ∷ C / [C]
  [casest′≡casesp″] = convEqTerm₂ [C] [C′] [C≡C′]
                                  (proj₂ (redSubst*Term ⊢casest′ [C′] (appTermNd [A] [C′] (▹▹-intr [▹▹AC′]) ⊩u″ [pa′])))

  [u∘pa≡] : Γ ⊩⟨ l ⟩ u ∘ pa ≡ u′ ∘ pa′ ∷ C / [C]
  [u∘pa≡] = app-congTermNd [A] [C] (▹▹-intr [▹▹AC]) [u≡u′] [pa] [pa′] [pa≡pa′]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C] [C′] [C≡C′]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₂ₜ₌ p p′ d d′ p≅p′ e f pa pa′ i j x) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm [C] [casest≡casesp] (transEqTerm [C] [v∘pa≡] (symEqTerm [C] [casest′≡casesp′]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

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

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases C t u v ≡ v ∘ pa ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term (cases-subst*ᵣ ⊢A ⊢B (escape [C])
                                                        (escapeTerm (▹▹-intr [▹▹AC]) ⊩u)
                                                        (escapeTerm (▹▹-intr [▹▹BC]) ⊩v)
                                                        (escapeTerm [B] [pa])
                                                        (redₜ d) i)
                                          [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) ⊩v [pa]))

  [▹▹AC′] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C′
  [▹▹AC′] = ≡⊩▹▹ {Γ = Γ} {l} {A} {C} {C′} [C′] [▹▹AC]

  [▹▹BC′] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C′
  [▹▹BC′] = ≡⊩▹▹ {Γ = Γ} {l} {B} {C} {C′} [C′] [▹▹BC]

  [▹▹AC≡′] : Γ ⊩⟨ l ⟩ A ▹▹ C ≡ A ▹▹ C′ / ▹▹-intr [▹▹AC]
  [▹▹AC≡′] = ⊩▹▹-cong [A] [C] [C′] [C≡C′] [▹▹AC]

  [▹▹BC≡′] : Γ ⊩⟨ l ⟩ B ▹▹ C ≡ B ▹▹ C′ / ▹▹-intr [▹▹BC]
  [▹▹BC≡′] = ⊩▹▹-cong [B] [C] [C′] [C≡C′] [▹▹BC]

  ⊩u″ : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C′ / ▹▹-intr [▹▹AC′]
  ⊩u″ = convTerm₁ (▹▹-intr [▹▹AC]) (▹▹-intr [▹▹AC′]) [▹▹AC≡′] ⊩u′

  ⊩v″ : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C′ / ▹▹-intr [▹▹BC′]
  ⊩v″ = convTerm₁ (▹▹-intr [▹▹BC]) (▹▹-intr [▹▹BC′]) [▹▹BC≡′] ⊩v′

  ⊢casest′ : Γ ⊢ cases C′ t′ u′ v′ ⇒* v′ ∘ pa′ ∷ C′
  ⊢casest′ = cases-subst*ᵣ ⊢A ⊢B (escape [C′])
                                 (escapeTerm (▹▹-intr [▹▹AC′]) ⊩u″)
                                 (escapeTerm (▹▹-intr [▹▹BC′]) ⊩v″)
                                 (escapeTerm [B] [pa′])
                                 (redₜ d′) j

  [casest′≡casesp′] : Γ ⊩⟨ l ⟩ cases C′ t′ u′ v′ ≡ v′ ∘ pa′ ∷ C / [C]
  [casest′≡casesp′] = convEqTerm₂ [C] [C′] [C≡C′]
                                  (proj₂ (redSubst*Term ⊢casest′ [C′] (appTermNd [B] [C′] (▹▹-intr [▹▹BC′]) ⊩v″ [pa′])))

  [v∘pa≡] : Γ ⊩⟨ l ⟩ v ∘ pa ≡ v′ ∘ pa′ ∷ C / [C]
  [v∘pa≡] = app-congTermNd [B] [C] (▹▹-intr [▹▹BC]) [v≡v′] [pa] [pa′] [pa≡pa′]
cases-cong′ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {t} {t′} {u} {u′} {v} {v′} {l} {l′} [C] [C′] [C≡C′]
          [∪AB]@(noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B']))
          [▹▹AC] [▹▹BC]
          [t≡t′]@(∪₃ₜ₌ p p′ d d′ p≅p′ e f (neNfₜ₌ neK neK′ k≡k)) [u≡u′] [v≡v′]
  with ∪-PE-injectivity (whnfRed* (red D) ∪ₙ)
... | PE.refl , PE.refl =
  transEqTerm [C] [casest≡casesp] (transEqTerm [C] [casesp≡casesp′] (symEqTerm [C] [casest′≡casesp′]))
  where
  [A] : Γ ⊩⟨ l′ ⟩ A
  [A] = irrelevance′ (wk-id A) ([A'] id (wf ⊢A))

  [B] : Γ ⊩⟨ l′ ⟩ B
  [B] = irrelevance′ (wk-id B) ([B'] id (wf ⊢B))

  [u] : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u] = ⊩ₗ (▹▹-intr [▹▹AC]) [u≡u′]

  [v] : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v] = ⊩ₗ (▹▹-intr [▹▹BC]) [v≡v′]

  [u′] : Γ ⊩⟨ l ⟩ u′ ∷ A ▹▹ C / ▹▹-intr [▹▹AC]
  [u′] = ⊩ᵣ (▹▹-intr [▹▹AC]) [u≡u′]

  [v′] : Γ ⊩⟨ l ⟩ v′ ∷ B ▹▹ C / ▹▹-intr [▹▹BC]
  [v′] = ⊩ᵣ (▹▹-intr [▹▹BC]) [v≡v′]

  nc : Neutral (cases C p u v)
  nc = casesₙ neK

  nc′ : Neutral (cases C′ p′ u′ v′)
  nc′ = casesₙ neK′

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

  redc : Γ ⊢ cases C t u v ⇒* cases C p u v ∷ C
  redc = cases-subst* ⊢A ⊢B ⊢C (escapeTerm (▹▹-intr [▹▹AC]) [u]) (escapeTerm (▹▹-intr [▹▹BC]) [v]) (redₜ d)

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

  redc′ : Γ ⊢ cases C′ t′ u′ v′ ⇒* cases C′ p′ u′ v′ ∷ C′
  redc′ = cases-subst* ⊢A ⊢B (escape [C′]) (escapeTerm (▹▹-intr [▹▹AC′]) ⊩u″) (escapeTerm (▹▹-intr [▹▹BC′]) ⊩v″) (redₜ d′)

  ⊢c : Γ ⊢ cases C p u v ∷ C
  ⊢c = redSecond*Term redc

  ⊢c′ : Γ ⊢ cases C′ p′ u′ v′ ∷ C′
  ⊢c′ = redSecond*Term redc′

  ⊢c″ : Γ ⊢ cases C′ p′ u′ v′ ∷ C
  ⊢c″ = conv ⊢c′ (sym ⊢C≡C′)

  vc : Γ ⊩⟨ l ⟩ cases C p u v ∷ C / [C]
  vc = neuTerm [C] nc ⊢c (~-cases ⊢A ⊢B ⊢C≅C (~-trans k≡k (~-sym k≡k))
                                  (escapeTermEq (▹▹-intr [▹▹AC]) (reflEqTerm (▹▹-intr [▹▹AC]) [u]))
                                  (escapeTermEq (▹▹-intr [▹▹BC]) (reflEqTerm (▹▹-intr [▹▹BC]) [v])))

  vc′ : Γ ⊩⟨ l ⟩ cases C′ p′ u′ v′ ∷ C′ / [C′]
  vc′ = neuTerm [C′] nc′ ⊢c′ (~-cases ⊢A ⊢B ⊢C′≅C′ (~-trans (~-sym k≡k) k≡k)
                                      (escapeTermEq (▹▹-intr [▹▹AC′]) (reflEqTerm (▹▹-intr [▹▹AC′]) ⊩u″))
                                      (escapeTermEq (▹▹-intr [▹▹BC′]) (reflEqTerm (▹▹-intr [▹▹BC′]) ⊩v″)))

  [casest≡casesp] : Γ ⊩⟨ l ⟩ cases C t u v ≡ cases C p u v ∷ C / [C]
  [casest≡casesp] = proj₂ (redSubst*Term redc [C] vc)

  [casest′≡casesp′] : Γ ⊩⟨ l ⟩ cases C′ t′ u′ v′ ≡ cases C′ p′ u′ v′ ∷ C / [C]
  [casest′≡casesp′] = convEqTerm₂ [C] [C′] [C≡C′] (proj₂ (redSubst*Term redc′ [C′] vc′))

  [casesp≡casesp′] : Γ ⊩⟨ l ⟩ cases C p u v ≡ cases C′ p′ u′ v′ ∷ C / [C]
  [casesp≡casesp′] = neuEqTerm [C] nc nc′ ⊢c ⊢c″
                       (~-cases ⊢A ⊢B ⊢C≅C′ k≡k (escapeTermEq (▹▹-intr [▹▹AC]) [u≡u′])
                                                (escapeTermEq (▹▹-intr [▹▹BC]) [v≡v′]))
cases-cong′ [C] [C′]⊆ [C≡C′] (emb 0<1 x) [▹▹AC] [▹▹BC] [t≡t′] [u≡u′] [v≡v′] =
  cases-cong′ [C] [C′]⊆ [C≡C′] x [▹▹AC] [▹▹BC] [t≡t′] [u≡u′] [v≡v′]

cases-cong″ : ∀ {A B C C′ t t′ u u′ v v′ l l′}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([C′]   : Γ ⊩⟨ l ⟩ C′)
            ([C≡C′] : Γ ⊩⟨ l ⟩ C ≡ C′ / [C])
            ([∪AB]  : Γ ⊩⟨ l′ ⟩ A ∪ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ A ∪ B / [∪AB])
            ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [▹▹AC])
            ([v≡v'] : Γ ⊩⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C t u v ≡ cases C′ t′ u′ v′ ∷ C / [C]
cases-cong″ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {t} {t′} {u} {u′} {v} {v′} {l} {l′}
            [C] [C′] [C≡C′] [∪AB] [▹▹AC] [▹▹BC] [t≡t′]
            [u≡u′] [v≡v′] =
  cases-cong′ [C] [C′] [C≡C′] (∪-elim [∪AB]) (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC])
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

-- Validity of cases
casesᵛ : ∀ {Γ : Con Term n} {A B C t u v l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
         ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
         ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
         → Γ ⊩ᵛ⟨ l ⟩ cases C t u v ∷ C / [Γ] / [C]
casesᵛ {Γ = Γ} {A} {B} {C} {t} {u} {v} {l} [Γ] [A] [B] [C] [t] [u] [v] {k = k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [∪AB]  = ∪ᵛ {F = A} {B} [Γ] [A] [B]
      [▹▹AC] = ▹▹ᵛ {F = A} {C} [Γ] [A] [C]
      [▹▹BC] = ▹▹ᵛ {F = B} {C} [Γ] [B] [C]
      σcases : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → Δ ⊩⟨ l ⟩ subst σ (cases C t u v) ∷ subst σ C / proj₁ ([C] ⊢Δ [σ])
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
            [σC′]    = proj₁ ([C] ⊢Δ [σ′])
            [σC≡C′]  = proj₂ ([C] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σ∪AB]   = proj₁ ([∪AB] ⊢Δ [σ])
            [σ▹▹AC]  = proj₁ ([▹▹AC] ⊢Δ [σ])
            [σ▹▹BC]  = proj₁ ([▹▹BC] ⊢Δ [σ])
            [σt]     = proj₁ ([t] ⊢Δ [σ])
            [σt≡t′]  = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σu≡u′]  = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σv≡v′]  = proj₂ ([v] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  cases-cong″ [σC] [σC′] [σC≡C′] [σ∪AB]
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

cases-congᵛ : ∀ {n : Nat} {Γ : Con Term n} {A B C C′ t t′ u u′ v v′ l}
              ([Γ]    : ⊩ᵛ Γ)
              ([A]    : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              ([B]    : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
              ([C]    : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
              ([C′]   : Γ ⊩ᵛ⟨ l ⟩ C′ / [Γ])
              ([C≡C′] : Γ ⊩ᵛ⟨ l ⟩ C ≡ C′ / [Γ] / [C])
              ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
              ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
              ([v≡v'] : Γ ⊩ᵛ⟨ l ⟩ v ≡ v′ ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ cases C t u v ≡ cases C′ t′ u′ v′ ∷ C / [Γ] / [C]
cases-congᵛ {n = n} {Γ = Γ} {A} {B} {C} {C′} {t} {t′} {u} {u′} {v} {v′} {l}
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
  in  cases-cong″ ⊩σC ⊩σC′ ⊩σC≡C′ ⊩σ∪AB
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

cases-βₗ′ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ A / [A])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C (injl t) u v ≡ u ∘ t ∷ C / [C]
cases-βₗ′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  proj₂ (redSubst*Term (cases-subst*ₗ (escape [A]) (escape [B]) (escape [C])
                                      (escapeTerm (▹▹-intr [▹▹AC]) [u])
                                      (escapeTerm (▹▹-intr [▹▹BC]) [v])
                                      (escapeTerm [A] [t])
                                      (id (injlⱼ (escape [B]) (escapeTerm [A] [t]))) injlₙ)
                       [C] (appTermNd [A] [C] (▹▹-intr [▹▹AC]) [u] [t]))

cases-βₗ″ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ A / [A])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C (injl t) u v ≡ u ∘ t ∷ C / [C]
cases-βₗ″ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  cases-βₗ′ [C] [A] [B] (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC]) [t]
            (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
            (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

cases-βₗᵛ : ∀ {A B C t u v l}
            ([Γ] : ⊩ᵛ Γ)
            ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
            ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
            ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ cases C (injl t) u v ≡ u ∘ t ∷ C / [Γ] / [C]
cases-βₗᵛ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
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
  in cases-βₗ″ ⊩σC ⊩σA ⊩σB
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

cases-βᵣ′ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩▹▹ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩▹▹ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ B / [B])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / ▹▹-intr [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / ▹▹-intr [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C (injr t) u v ≡ v ∘ t ∷ C / [C]
cases-βᵣ′ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  proj₂ (redSubst*Term (cases-subst*ᵣ (escape [A]) (escape [B]) (escape [C])
                                      (escapeTerm (▹▹-intr [▹▹AC]) [u])
                                      (escapeTerm (▹▹-intr [▹▹BC]) [v])
                                      (escapeTerm [B] [t])
                                      (id (injrⱼ (escape [A]) (escapeTerm [B] [t]))) injrₙ)
                       [C] (appTermNd [B] [C] (▹▹-intr [▹▹BC]) [v] [t]))

cases-βᵣ″ : ∀ {A B C t u v l}
            ([C]    : Γ ⊩⟨ l ⟩ C)
            ([A]    : Γ ⊩⟨ l ⟩ A)
            ([B]    : Γ ⊩⟨ l ⟩ B)
            ([▹▹AC] : Γ ⊩⟨ l ⟩ A ▹▹ C)
            ([▹▹BC] : Γ ⊩⟨ l ⟩ B ▹▹ C)
            ([t]    : Γ ⊩⟨ l ⟩ t ∷ B / [B])
            ([u]    : Γ ⊩⟨ l ⟩ u ∷ A ▹▹ C / [▹▹AC])
            ([v]    : Γ ⊩⟨ l ⟩ v ∷ B ▹▹ C / [▹▹BC])
            → Γ ⊩⟨ l ⟩ cases C (injr t) u v ≡ v ∘ t ∷ C / [C]
cases-βᵣ″ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
          [C] [A] [B] [▹▹AC] [▹▹BC] [t] [u] [v] =
  cases-βᵣ′ [C] [A] [B] (▹▹-elim [▹▹AC]) (▹▹-elim [▹▹BC]) [t]
            (irrelevanceTerm [▹▹AC] (▹▹-intr (▹▹-elim [▹▹AC])) [u])
            (irrelevanceTerm [▹▹BC] (▹▹-intr (▹▹-elim [▹▹BC])) [v])

cases-βᵣᵛ : ∀ {A B C t u v l}
            ([Γ] : ⊩ᵛ Γ)
            ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
            ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B])
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
            ([v] : Γ ⊩ᵛ⟨ l ⟩ v ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
            → Γ ⊩ᵛ⟨ l ⟩ cases C (injr t) u v ≡ v ∘ t ∷ C / [Γ] / [C]
cases-βᵣᵛ {Γ = Γ} {A = A} {B = B} {C = C} {t} {u} {v} {l}
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
  in cases-βᵣ″ ⊩σC ⊩σA ⊩σB
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
