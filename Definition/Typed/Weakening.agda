module Definition.Typed.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties as UP
     using (wkIndex-step; wkIndex-lift; wk-β; wk-β-natrec)
open import Definition.Typed

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.HeterogeneousEquality as HE


-- Weakening type

mutual
  data _⊆_ : Con Term → Con Term → Set where
    id   : ∀ {Γ} → Γ ⊆ Γ
    step : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) →  Γ      ⊆ (Δ ∙ σ)
    lift : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ U.wk (toWk inc) σ)

  toWk : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Wk
  toWk id = id
  toWk (step ρ) = step (toWk ρ)
  toWk (lift ρ) = lift (toWk ρ)

wkₜ : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Term → Term
wkₜ ρ = U.wk (toWk ρ)

wkLiftₜ : ∀ {Γ Δ : Con Term} (ρ : Γ ⊆ Δ) → Term → Term
wkLiftₜ ρ = U.wk (lift (toWk ρ))


-- Weakening composition

mutual
  _•ₜ_ : ∀ {Γ Δ E} → Δ ⊆ E → Γ ⊆ Δ → Γ ⊆ E
  id     •ₜ η′ = η′
  step η •ₜ η′ = step (η •ₜ η′)
  lift η •ₜ id = lift η
  lift η •ₜ step η′ = step (η •ₜ η′)
  lift η •ₜ lift η′ =  PE.subst (λ x → _ ∙ _ ⊆ _ ∙ x)
                               (wk-comp-comm η η′)
                               (lift (η •ₜ η′))

  wk-comp-comm : ∀ {Γ Δ E σ} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
               → wkₜ (η •ₜ η′) σ PE.≡ wkₜ η (wkₜ η′ σ)
  wk-comp-comm {σ = σ} η η′ =
    PE.trans (PE.cong (λ x → U.wk x σ) (comp-eq η η′))
             (PE.sym (UP.wk-comp-comm (toWk η) (toWk η′) σ))

  comp-eq : ∀ {Γ Δ E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
          → toWk (η •ₜ η′) PE.≡ toWk η • toWk η′
  comp-eq id η′ = PE.refl
  comp-eq (step η) η′ = PE.cong step (comp-eq η η′)
  comp-eq (lift η) id = PE.refl
  comp-eq (lift η) (step η′) = PE.cong step (comp-eq η η′)
  comp-eq (lift {Δ} {E} {.(wkₜ η′ σ)} η) (lift {Γ} {.Δ} {σ} η′) =
    HE.≅-to-≡
      (HE.trans
        (HE.cong₂ (λ X → toWk {Γ ∙ σ} {X})
                  (HE.≡-to-≅ (PE.cong (λ x → E ∙ x)
                                      (PE.sym (wk-comp-comm η η′))))
                  (subst-eq η η′))
        (HE.≡-to-≅ (PE.cong lift (comp-eq η η′))) )

  subst-eq : ∀ {Γ Δ E σ} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
           → HE._≅_ {A = Γ ∙ σ ⊆ E ∙ wkₜ η (wkₜ η′ σ)}
                    (PE.subst (λ x → Γ ∙ σ ⊆ E ∙ x)
                              (wk-comp-comm η η′) (lift (η •ₜ η′)))
                    {B = Γ ∙ σ ⊆ E ∙ wkₜ (η •ₜ η′) σ}
                    (lift (η •ₜ η′))
  subst-eq η η′ = HE.≡-subst-removable (λ x → _ ∙ _ ⊆ _ ∙ x)
                                       (wk-comp-comm η η′) (lift (η •ₜ η′))

wk-comp-comm-lift : ∀ {Γ Δ E G} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ)
                  → wkLiftₜ (η •ₜ η′) G PE.≡ wkLiftₜ η (wkLiftₜ η′ G)
wk-comp-comm-lift {G = G} η η′ =
  PE.sym (PE.trans (UP.wk-comp-comm (lift (toWk η)) (lift (toWk η′)) G)
                   (PE.cong (λ x → U.wk (lift x) G) (PE.sym (comp-eq η η′))))

wk-comp-comm-subst : ∀ {Γ Δ E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) G
                   → wkLiftₜ (η •ₜ η′) G [ a ] PE.≡ wkLiftₜ η (wkLiftₜ η′ G) [ a ]
wk-comp-comm-subst {a = a} η η′ G = PE.cong (λ x → x [ a ]) (wk-comp-comm-lift {G = G} η η′)


-- Weakening of judgements

wkIndex : ∀ {Γ Δ n A} (ρ : Γ ⊆ Δ) →
        let ρA = U.wk (toWk ρ) A
            ρn = wkNat (toWk ρ) n
        in  ⊢ Δ → n ∷ A ∈ Γ → ρn ∷ ρA ∈ Δ
wkIndex id ⊢Δ i = PE.subst (λ x → _ ∷ x ∈ _) (PE.sym (UP.wk-id _ 0)) i
wkIndex (step ρ) (⊢Δ ∙ A) i = PE.subst (λ x → _ ∷ x ∈ _)
                                       (wkIndex-step (toWk ρ))
                                       (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) (⊢Δ ∙ A) (there i) = PE.subst (λ x → _ ∷ x ∈ _)
                                               (wkIndex-lift (toWk ρ))
                                               (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) ⊢Δ here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ∈ G)
               (wkIndex-lift (toWk ρ))
               here

mutual
  wk : ∀ {Γ Δ A} (ρ : Γ ⊆ Δ) →
     let ρA = U.wk (toWk ρ) A
     in  ⊢ Δ → Γ ⊢ A → Δ ⊢ ρA
  wk ρ ⊢Δ (ℕ ⊢Γ) = ℕ ⊢Δ
  wk ρ ⊢Δ (U ⊢Γ) = U ⊢Δ
  wk ρ ⊢Δ (Π F ▹ G) = let ρF = wk ρ ⊢Δ F
                      in  Π ρF ▹ (wk (lift ρ) (⊢Δ ∙ ρF) G)
  wk ρ ⊢Δ (univ A) = univ (wkTerm ρ ⊢Δ A)

  wkTerm : ∀ {Γ Δ A t} (ρ : Γ ⊆ Δ) →
         let ρA = U.wk (toWk ρ) A
             ρt = U.wk (toWk ρ) t
         in ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ ρt ∷ ρA
  wkTerm ρ ⊢Δ (ℕ ⊢Γ) = ℕ ⊢Δ
  wkTerm ρ ⊢Δ (Π F ▹ G) = let ρF = wkTerm ρ ⊢Δ F
                          in  Π ρF ▹ (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G)
  wkTerm ρ ⊢Δ (var ⊢Γ x) = var ⊢Δ (wkIndex ρ ⊢Δ x)
  wkTerm ρ ⊢Δ (lam F t) = let ρF = wk ρ ⊢Δ F
                          in lam ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) t)
  wkTerm ρ ⊢Δ (_∘_ {G = G} g a) = PE.subst (λ x → _ ⊢ _ ∷ x)
                                           (PE.sym (wk-β G))
                                           (wkTerm ρ ⊢Δ g ∘ wkTerm ρ ⊢Δ a)
  wkTerm ρ ⊢Δ (zero ⊢Γ) = zero ⊢Δ
  wkTerm ρ ⊢Δ (suc n) = suc (wkTerm ρ ⊢Δ n)
  wkTerm {Δ = Δ} ρ ⊢Δ (natrec {G = G} {s = s} ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (natrec (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢G)
                     (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) (wkTerm ρ ⊢Δ ⊢z))
                     (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                               (wk-β-natrec (toWk ρ) G)
                               (wkTerm ρ ⊢Δ ⊢s))
                     (wkTerm ρ ⊢Δ ⊢n))
  wkTerm ρ ⊢Δ (conv t A≡B) = conv (wkTerm ρ ⊢Δ t) (wkEq ρ ⊢Δ A≡B)

  wkEq : ∀ {Γ Δ A B} (ρ : Γ ⊆ Δ) →
       let ρA = U.wk (toWk ρ) A
           ρB = U.wk (toWk ρ) B
       in ⊢ Δ → Γ ⊢ A ≡ B → Δ ⊢ ρA ≡ ρB
  wkEq ρ ⊢Δ (univ A≡B) = univ (wkEqTerm ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (refl A) = refl (wk ρ ⊢Δ A)
  wkEq ρ ⊢Δ (sym A≡B) = sym (wkEq ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (trans A≡B B≡C) = trans (wkEq ρ ⊢Δ A≡B) (wkEq ρ ⊢Δ B≡C)
  wkEq ρ ⊢Δ (Π-cong F F≡H G≡E) = let ρF = wk ρ ⊢Δ F
                                 in  Π-cong ρF (wkEq ρ ⊢Δ F≡H)
                                               (wkEq (lift ρ) (⊢Δ ∙ ρF) G≡E)

  wkEqTerm : ∀ {Γ Δ A t u} (ρ : Γ ⊆ Δ) →
           let ρA = U.wk (toWk ρ) A
               ρt = U.wk (toWk ρ) t
               ρu = U.wk (toWk ρ) u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ ρt ≡ ρu ∷ ρA
  wkEqTerm ρ ⊢Δ (refl t) = refl (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (sym t≡u) = sym (wkEqTerm ρ ⊢Δ t≡u)
  wkEqTerm ρ ⊢Δ (trans t≡u u≡r) = trans (wkEqTerm ρ ⊢Δ t≡u) (wkEqTerm ρ ⊢Δ u≡r)
  wkEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (wkEqTerm ρ ⊢Δ t≡u) (wkEq ρ ⊢Δ A≡B)
  wkEqTerm ρ ⊢Δ (Π-cong F F≡H G≡E) =
    let ρF = wk ρ ⊢Δ F
    in  Π-cong ρF (wkEqTerm ρ ⊢Δ F≡H)
                  (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm ρ ⊢Δ f≡g) (wkEqTerm ρ ⊢Δ a≡b))
  wkEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {G = G} F ⊢t ⊢a) =
    let ρF = wk ρ ⊢Δ F
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x → _ ⊢ U.wk (toWk ρ) ((lam t) ∘ a) ≡ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (wkTerm ρ ⊢Δ ⊢a)))
  wkEqTerm ρ ⊢Δ (fun-ext F f g f0≡g0) =
    let ρF = wk ρ ⊢Δ F
    in  fun-ext ρF (wkTerm ρ ⊢Δ f)
                   (wkTerm ρ ⊢Δ g)
                   (PE.subst (λ t → _ ⊢ t ∘ _ ≡ _ ∷ _)
                             (PE.sym (wkIndex-lift (toWk ρ)))
                             (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ∷ _)
                                       (PE.sym (wkIndex-lift (toWk ρ)))
                                       (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) f0≡g0)))
  wkEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (wkEqTerm ρ ⊢Δ m≡n)
  wkEqTerm {Δ = Δ} ρ ⊢Δ (natrec-cong {s = s} {s' = s'} {F = F}
                                     F≡F' z≡z' s≡s' n≡n') =
    PE.subst (λ x → Δ ⊢ natrec _ _ _ _ ≡ _ ∷ x) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) F≡F')
                          (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x) (wk-β F)
                                    (wkEqTerm ρ ⊢Δ z≡z'))
                          (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s
                                             ≡ U.wk (toWk ρ) s' ∷ x)
                                    (wk-β-natrec (toWk ρ) F)
                                    (wkEqTerm ρ ⊢Δ s≡s'))
                          (wkEqTerm ρ ⊢Δ n≡n'))
  wkEqTerm {Δ = Δ} ρ ⊢Δ (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec (U.wk (lift (toWk ρ)) F) _ _ _ ≡ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) z ∷ x)
                                    (wk-β F)
                                    (wkTerm ρ ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                                    (wk-β-natrec (toWk ρ) F)
                                    (wkTerm ρ ⊢Δ ⊢s)))
  wkEqTerm {Δ = Δ} ρ ⊢Δ (natrec-suc {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec (U.wk (lift (toWk ρ)) F) _ _ _
                      ≡ _ ∘ (natrec _ _ _ _) ∷ x)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm ρ ⊢Δ ⊢n)
                         (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢F)
                         (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) z ∷ x)
                                   (wk-β F)
                                   (wkTerm ρ ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                                   (wk-β-natrec (toWk ρ) F)
                                   (wkTerm ρ ⊢Δ ⊢s)))

mutual
  wkRed : ∀ {Γ Δ A B} (ρ : Γ ⊆ Δ) →
           let ρA = U.wk (toWk ρ) A
               ρB = U.wk (toWk ρ) B
           in ⊢ Δ → Γ ⊢ A ⇒ B → Δ ⊢ ρA ⇒ ρB
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : ∀ {Γ Δ A t u} → (ρ : Γ ⊆ Δ) →
           let ρA = U.wk (toWk ρ) A
               ρt = U.wk (toWk ρ) t
               ρu = U.wk (toWk ρ) u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ ρt ⇒ ρu ∷ ρA
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {B = B} t⇒u a) =
    PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a))
  wkRedTerm ρ ⊢Δ (β-red {A} {B} {a} {t} ⊢A ⊢t ⊢a) =
    let ⊢ρA = wk ρ ⊢Δ ⊢A
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ ⊢ U.wk (toWk ρ) ((lam t) ∘ a) ⇒ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ⊢ρA (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (wkTerm ρ ⊢Δ ⊢a)))
  wkRedTerm {Δ = Δ} ρ ⊢Δ (natrec-subst {s = s} {F = F} ⊢F ⊢z ⊢s n⇒n') =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β F))
             (natrec-subst (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β F)
                                     (wkTerm ρ ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                                     (wk-β-natrec (toWk ρ) F)
                                     (wkTerm ρ ⊢Δ ⊢s))
                           (wkRedTerm ρ ⊢Δ n⇒n'))
  wkRedTerm {Δ = Δ} ρ ⊢Δ (natrec-zero {s = s} {F = F} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec (U.wk (lift (toWk ρ)) F) _ _ _ ⇒ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm ρ ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                                    (wk-β-natrec (toWk ρ) F)
                                    (wkTerm ρ ⊢Δ ⊢s)))
  wkRedTerm {Δ = Δ} ρ ⊢Δ (natrec-suc {s = s} {F = F} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm ρ ⊢Δ ⊢n)
                         (wk (lift ρ) (⊢Δ ∙ ℕ ⊢Δ) ⊢F)
                         (PE.subst (λ x → _ ⊢ _ ∷ x)
                                   (wk-β F)
                                   (wkTerm ρ ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk (toWk ρ) s ∷ x)
                                   (wk-β-natrec (toWk ρ) F)
                                   (wkTerm ρ ⊢Δ ⊢s)))

wkRed* : ∀ {Γ Δ A B} → (ρ : Γ ⊆ Δ) →
           let ρA = U.wk (toWk ρ) A
               ρB = U.wk (toWk ρ) B
           in ⊢ Δ → Γ ⊢ A ⇒* B → Δ ⊢ ρA ⇒* ρB
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A' ⇨ A'⇒*B) = wkRed ρ ⊢Δ A⇒A' ⇨ wkRed* ρ ⊢Δ A'⇒*B

wkRed*Term : ∀ {Γ Δ A t u} → (ρ : Γ ⊆ Δ) →
           let ρA = U.wk (toWk ρ) A
               ρt = U.wk (toWk ρ) t
               ρu = U.wk (toWk ρ) u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ ρt ⇒* ρu ∷ ρA
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t' ⇨ t'⇒*u) = wkRedTerm ρ ⊢Δ t⇒t' ⇨ wkRed*Term ρ ⊢Δ t'⇒*u

wkRed:*: : ∀ {Γ Δ A B} → (ρ : Γ ⊆ Δ) →
         let ρA = U.wk (toWk ρ) A
             ρB = U.wk (toWk ρ) B
         in ⊢ Δ → Γ ⊢ A :⇒*: B → Δ ⊢ ρA :⇒*: ρB
wkRed:*: ρ ⊢Δ [ ⊢A , ⊢B , D ] = [ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]

wkRed:*:Term : ∀ {Γ Δ A t u} → (ρ : Γ ⊆ Δ) →
             let ρA = U.wk (toWk ρ) A
                 ρt = U.wk (toWk ρ) t
                 ρu = U.wk (toWk ρ) u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A → Δ ⊢ ρt :⇒*: ρu ∷ ρA
wkRed:*:Term ρ ⊢Δ [ ⊢t , ⊢u , d ] =
  [ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]
