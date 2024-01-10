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
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C] (noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B'])) [▹▹AC] [▹▹BC] (∪₁ₜ p d ep pa i x) [u] [v]
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
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C] (noemb (∪ᵣ A' B' D ⊢A ⊢B A≡A [A'] [B'])) [▹▹AC] [▹▹BC] (∪₂ₜ p d ep pa i x) [u] [v]
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
cases′ {Γ = Γ} {A = A} {B = B} {C = C} {t = t} {u = u} {v = v} {l} {l′} [C] (noemb (∪ᵣ A' B' [ ⊢AB , ⊢AB' , D ] ⊢A' ⊢B' A≡A [A'] [B'])) [▹▹AC] [▹▹BC] (∪₃ₜ p [ ⊢t , ⊢p , d ] ep (neNfₜ neK ⊢k k≡k)) [u] [v] =
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

{--
fst-cong′ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ ⟩ Σ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / B-intr BΣ [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong′ {Γ = Γ} {F = F} {G = G} [F]
          [ΣFG]@(noemb (Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
          [t≡t′]@(Σₜ₌ p p′ d d′ pProd pProd′ p≅p′ [t] [t′] [fstp] [fstp′] [fst≡] [snd≡]) with
            B-PE-injectivity BΣ (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl =
  let ⊢Γ = wf ⊢F
      [fstp]₁ = irrelevanceTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fstp]
      [fstp′]₁ = irrelevanceTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fstp′]
      [fst≡]₁ = irrelevanceEqTerm′ (wk-id F) ([F'] id ⊢Γ) [F] [fst≡]
      [fstt≡fstp] = proj₂ (redSubst*Term (fst-subst* ⊢F ⊢G (redₜ d)) [F] [fstp]₁)
      [fstt′≡fstp′] = proj₂ (redSubst*Term (fst-subst* ⊢F ⊢G (redₜ d′)) [F] [fstp′]₁)
  in  transEqTerm [F] [fstt≡fstp] (transEqTerm [F] [fst≡]₁ (symEqTerm [F] [fstt′≡fstp′]))
fst-cong′ [F] (emb 0<1 x) = fst-cong′ [F] x

-- Reducibility of congruence of fst
fst-cong″ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong″ {F = F} {G} [F] [ΣFG] [t≡t′] =
  let [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ (Σ-elim [ΣFG])) [t≡t′]
  in  fst-cong′ [F] (Σ-elim [ΣFG]) [t≡t′]

fst-congᵛ : ∀ {F G t t′ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
          → Γ ⊩ᵛ⟨ l ⟩ fst t ≡ fst t′ ∷ F / [Γ] / [F]
fst-congᵛ {F = F} {G} [Γ] [F] [G] [t] [t′] [t≡t′] ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      ⊩σF = proj₁ ([F] ⊢Δ [σ])
      ⊩σΣFG = proj₁ ([ΣFG] ⊢Δ [σ])
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
  in  fst-cong″ ⊩σF ⊩σΣFG ⊩σt≡t′
--}

-- Validity of cases
casesᵛ : ∀ {Γ : Con Term n} {A B C t u v l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
         ([C] : Γ ⊩ᵛ⟨ l ⟩ C / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ∪ B / [Γ] / ∪ᵛ {F = A} {B} [Γ] [A] [B])
         ([u] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ C / [Γ] / ▹▹ᵛ {F = A} {C} [Γ] [A] [C])
         ([v] : Γ ⊩ᵛ⟨ l ⟩ t ∷ B ▹▹ C / [Γ] / ▹▹ᵛ {F = B} {C} [Γ] [B] [C])
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
        in cases″ ⊩σC ⊩σ∪AB {!⊩σ▹▹AC!} {!⊩σ▹▹BC!} ⊩σt ⊩σu ⊩σv
  in  σcases ⊢Δ [σ] ,
      {!!}
 {--
      (λ {σ′} [σ′] [σ≡σ′] →
        let [σF] = proj₁ ([F] ⊢Δ [σ])
            [σΣFG] = proj₁ ([ΣFG] ⊢Δ [σ])
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  fst-cong″ [σF] [σΣFG] [σt≡σ′t])
--}
