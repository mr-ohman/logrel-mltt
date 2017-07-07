{-# OPTIONS --without-K #-}

module Definition.Untyped.Properties where

open import Tools.Nat
open import Tools.Unit
open import Tools.PropositionalEquality as PE hiding (subst)

open import Definition.Untyped


-- Weakening properties

-- If two weakenings are equal under wkNat, then they are equal when lifted.
wkVar-lift : ∀ {ρ ρ'} → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
           → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ') x)
wkVar-lift eq zero = refl
wkVar-lift eq (suc x) = cong suc (eq x)

-- If two weakenings are equal under wkNat, then they are equal under wk.
wkVar-to-wk : ∀ {ρ ρ'} → (∀ x → wkVar ρ x ≡ wkVar ρ' x)
     → (t : Term) → wk ρ t ≡ wk ρ' t
wkVar-to-wk eq U = refl
wkVar-to-wk eq (Π t ▹ t₁) =
  cong₂ Π_▹_ (wkVar-to-wk eq t) (wkVar-to-wk (wkVar-lift eq) t₁)
wkVar-to-wk eq ℕ = refl
wkVar-to-wk eq (var x) = cong var (eq x)
wkVar-to-wk eq (lam t) = cong lam (wkVar-to-wk (wkVar-lift eq) t)
wkVar-to-wk eq (t ∘ t₁) = cong₂ _∘_ (wkVar-to-wk eq t) (wkVar-to-wk eq t₁)
wkVar-to-wk eq zero = refl
wkVar-to-wk eq (suc t) = cong suc (wkVar-to-wk eq t)
wkVar-to-wk eq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (wkVar-to-wk (wkVar-lift eq) t)
               (wkVar-to-wk eq t₁) (wkVar-to-wk eq t₂) (wkVar-to-wk eq t₃)

-- lift id is the same as id.
wkVar-lift-id : (x : Nat) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id zero = refl
wkVar-lift-id (suc x) = refl

-- id is the identity.
wkVar-id : (x : Nat) → wkVar id x ≡ x
wkVar-id x = refl

wk-id : (t : Term) → wk id t ≡ t
wk-id U = refl
wk-id (Π t ▹ t₁) =
  cong₂ Π_▹_ (wk-id t) (trans (wkVar-to-wk wkVar-lift-id t₁) (wk-id t₁))
wk-id ℕ = refl
wk-id (var x) = cong var (wkVar-id x)
wk-id (lam t) = cong lam (trans (wkVar-to-wk wkVar-lift-id t) (wk-id t))
wk-id (t ∘ t₁) = cong₂ _∘_ (wk-id t) (wk-id t₁)
wk-id zero = refl
wk-id (suc t) = cong suc (wk-id t)
wk-id (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (wkVar-to-wk wkVar-lift-id t) (wk-id t))
               (wk-id t₁) (wk-id t₂) (wk-id t₃)

wk-lift-id : (t : Term) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

-- Composition of weakenings
wkVar-comp : ∀ ρ ρ' x → wkVar ρ (wkVar ρ' x) ≡ wkVar (ρ • ρ') x
wkVar-comp id ρ' x = refl
wkVar-comp (step ρ) ρ' x = cong suc (wkVar-comp ρ ρ' x)
wkVar-comp (lift ρ) id x = refl
wkVar-comp (lift ρ) (step ρ') x = cong suc (wkVar-comp ρ ρ' x)
wkVar-comp (lift ρ) (lift ρ') zero = refl
wkVar-comp (lift ρ) (lift ρ') (suc x) = cong suc (wkVar-comp ρ ρ' x)

wk-comp : ∀ ρ ρ' t → wk ρ (wk ρ' t) ≡ wk (ρ • ρ') t
wk-comp ρ ρ' U = refl
wk-comp ρ ρ' (Π t ▹ t₁) =
  cong₂ Π_▹_ (wk-comp ρ ρ' t) (wk-comp (lift ρ) (lift ρ') t₁)
wk-comp ρ ρ' ℕ = refl
wk-comp ρ ρ' (var x) = cong var (wkVar-comp ρ ρ' x)
wk-comp ρ ρ' (lam t) = cong lam (wk-comp (lift ρ) (lift ρ') t)
wk-comp ρ ρ' (t ∘ t₁) = cong₂ _∘_ (wk-comp ρ ρ' t) (wk-comp ρ ρ' t₁)
wk-comp ρ ρ' zero = refl
wk-comp ρ ρ' (suc t) = cong suc (wk-comp ρ ρ' t)
wk-comp ρ ρ' (natrec t t₁ t₂ t₃) =
  cong₄ natrec (wk-comp (lift ρ) (lift ρ') t)
               (wk-comp ρ ρ' t₁)
               (wk-comp ρ ρ' t₂)
               (wk-comp ρ ρ' t₃)

lift-step-comp : (ρ : Wk) → step id • ρ ≡ lift ρ • step id
lift-step-comp id = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

wk1-wk : ∀ ρ t → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : ∀ ρ t → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : ∀ ρ t → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))

-- Substitution properties

substVar-lift : ∀ {σ σ'} → ((x : Nat) → σ x ≡ σ' x)
            → (x : Nat) → liftSubst σ x ≡ liftSubst σ' x
substVar-lift eq zero = refl
substVar-lift eq (suc x) = cong wk1 (eq x)

substVar-to-subst : ∀ {σ σ'} → ((x : Nat) → σ x ≡ σ' x)
        → (t : Term) → subst σ t ≡ subst σ' t
substVar-to-subst eq U = refl
substVar-to-subst eq (Π t ▹ t₁) =
  cong₂ Π_▹_ (substVar-to-subst eq t) (substVar-to-subst (substVar-lift eq) t₁)
substVar-to-subst eq ℕ = refl
substVar-to-subst eq (var x₁) = eq x₁
substVar-to-subst eq (lam t) = cong lam (substVar-to-subst (substVar-lift eq) t)
substVar-to-subst eq (t ∘ t₁) =
  cong₂ _∘_ (substVar-to-subst eq t) (substVar-to-subst eq t₁)
substVar-to-subst eq zero = refl
substVar-to-subst eq (suc t) = cong suc (substVar-to-subst eq t)
substVar-to-subst eq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (substVar-to-subst (substVar-lift eq) t)
               (substVar-to-subst eq t₁)
               (substVar-to-subst eq t₂)
               (substVar-to-subst eq t₃)

subst-lift-id : (x : Nat) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id zero = refl
subst-lift-id (suc x) = refl

subst-id : (t : Term) → subst idSubst t ≡ t
subst-id U = refl
subst-id (Π t ▹ t₁) =
  cong₂ Π_▹_ (subst-id t) (trans (substVar-to-subst subst-lift-id t₁) (subst-id t₁))
subst-id ℕ = refl
subst-id (var x) = refl
subst-id (lam t) = cong lam (trans (substVar-to-subst subst-lift-id t) (subst-id t))
subst-id (t ∘ t₁) = cong₂ _∘_ (subst-id t) (subst-id t₁)
subst-id zero = refl
subst-id (suc t) = cong suc (subst-id t)
subst-id (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (substVar-to-subst subst-lift-id t) (subst-id t))
               (subst-id t₁) (subst-id t₂) (subst-id t₃)


-- Weakening and substitution composition

subst-lift-•ₛ : ∀ {ρ σ} t
              → subst (lift ρ •ₛ liftSubst σ) t
              ≡ subst (liftSubst (ρ •ₛ σ)) t
subst-lift-•ₛ =
  substVar-to-subst (λ { zero → refl ; (suc x) → sym (wk1-wk≡lift-wk1 _ _)})

subst-lift-ₛ• : ∀ {ρ σ} t
              → subst (liftSubst σ ₛ• lift ρ) t
              ≡ subst (liftSubst (σ ₛ• ρ)) t
subst-lift-ₛ• = substVar-to-subst (λ { zero → refl ; (suc x) → refl})

wk-subst : ∀ {σ ρ} t → wk σ (subst ρ t) ≡ subst (σ •ₛ ρ) t
wk-subst U = refl
wk-subst (Π t ▹ t₁) =
  cong₂ Π_▹_ (wk-subst t) (trans (wk-subst t₁) (subst-lift-•ₛ t₁))
wk-subst ℕ = refl
wk-subst (var x) = refl
wk-subst (lam t) = cong lam (trans (wk-subst t) (subst-lift-•ₛ t))
wk-subst (t ∘ t₁) = cong₂ _∘_ (wk-subst t) (wk-subst t₁)
wk-subst zero = refl
wk-subst (suc t) = cong suc (wk-subst t)
wk-subst (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (wk-subst t) (subst-lift-•ₛ t))
               (wk-subst t₁) (wk-subst t₂) (wk-subst t₃)

subst-wk : ∀ {σ ρ} t → subst ρ (wk σ t) ≡ subst (ρ ₛ• σ) t
subst-wk U = refl
subst-wk (Π t ▹ t₁) =
  cong₂ Π_▹_ (subst-wk t) (trans (subst-wk t₁) (subst-lift-ₛ• t₁))
subst-wk ℕ = refl
subst-wk (var x) = refl
subst-wk (lam t) = cong lam (trans (subst-wk t) (subst-lift-ₛ• t))
subst-wk (t ∘ t₁) = cong₂ _∘_ (subst-wk t) (subst-wk t₁)
subst-wk zero = refl
subst-wk (suc t) = cong suc (subst-wk t)
subst-wk (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (subst-wk t) (subst-lift-ₛ• t))
               (subst-wk t₁) (subst-wk t₂) (subst-wk t₃)

wk-subst-lift : ∀ {ρ σ} G
              → wk (lift ρ) (subst (liftSubst σ) G)
              ≡ subst (liftSubst (ρ •ₛ σ)) G
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

wk≡subst : ∀ ρ t → wk ρ t ≡ subst (toSubst ρ) t
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)


-- Composition of substitution

substCompLift : ∀ {σ σ'} x
              → (liftSubst σ ₛ•ₛ liftSubst σ') x
              ≡ (liftSubst (σ ₛ•ₛ σ')) x
substCompLift zero = refl
substCompLift {σ} {σ'} (suc x) = trans (subst-wk (σ' x)) (sym (wk-subst (σ' x)))

substCompEq : ∀ {σ σ'} (t : Term)
            → subst σ (subst σ' t) ≡ subst (σ ₛ•ₛ σ') t
substCompEq U = refl
substCompEq (Π t ▹ t₁) =
  cong₂ Π_▹_ (substCompEq t) (trans (substCompEq t₁) (substVar-to-subst substCompLift t₁))
substCompEq ℕ = refl
substCompEq (var x) = refl
substCompEq (lam t) = cong lam (trans (substCompEq t) (substVar-to-subst substCompLift t))
substCompEq (t ∘ t₁) = cong₂ _∘_ (substCompEq t) (substCompEq t₁)
substCompEq zero = refl
substCompEq (suc t) = cong suc (substCompEq t)
substCompEq (natrec t t₁ t₂ t₃) =
  cong₄ natrec (trans (substCompEq t) (substVar-to-subst substCompLift t))
               (substCompEq t₁) (substCompEq t₂) (substCompEq t₃)


-- Specific equalities

wk-comp-subst : ∀ {a} ρ ρ' G
                   → wk (lift (ρ • ρ')) G [ a ] ≡ wk (lift ρ) (wk (lift ρ') G) [ a ]
wk-comp-subst {a} ρ ρ' G =
  cong (λ x → x [ a ]) (sym (wk-comp (lift ρ) (lift ρ') G))

-- Beta reduction weakening

wk-β : ∀ {pr a} t → wk pr (t [ a ]) ≡ wk (lift pr) t [ wk pr a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t)))

wk-β↑ : ∀ {ρ a} t → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t)))

-- Natrec beta-reduction weakening

wk-β-natrec : ∀ ρ G
  → Π ℕ ▹ (Π wk (lift ρ) G ▹ wk (lift (lift ρ)) (wk1 (G [ suc (var zero) ]↑)))
  ≡ Π ℕ ▹ (wk (lift ρ) G ▹▹ wk (lift ρ) G [ suc (var zero) ]↑)
wk-β-natrec ρ G =
  cong₂ Π_▹_ refl (cong₂ Π_▹_ refl
    (trans (wk-comp (lift (lift ρ)) (step id)
                    (subst (consSubst (wk1Subst var) (suc (var zero))) G))
       (trans (wk-subst G) (sym (trans (wk-subst (wk (lift ρ) G))
         (trans (subst-wk G)
                (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)))))))

substVarSingletonComp : ∀ {a σ} (x : Nat)
                     → (consSubst idSubst a ₛ•ₛ liftSubst σ) x
                     ≡ (consSubst σ a) x
substVarSingletonComp zero = refl
substVarSingletonComp {σ = σ} (suc x) = trans (subst-wk (σ x)) (subst-id (σ x))

substSingletonComp : ∀ {a σ} t
                     → subst (consSubst idSubst a ₛ•ₛ liftSubst σ) t
                     ≡ subst (consSubst σ a) t
substSingletonComp = substVar-to-subst substVarSingletonComp

-- substConcatSingleton' : ∀ {a σ} (x : Nat)
--                       → (σ ₛ•ₛ consSubst idSubst a) x
--                       ≡ (consSubst σ (subst σ a)) x
-- substConcatSingleton' zero = refl
-- substConcatSingleton' (suc x) = refl

-- substConcatSingleton'' : ∀ {a σ} (x : Nat)
--                        → (σ ₛ•ₛ consSubst (wk1Subst idSubst) a) x
--                        ≡ (consSubst (tail σ) (subst σ a)) x
-- substConcatSingleton'' zero = refl
-- substConcatSingleton'' (suc x) = refl

singleSubstComp : ∀ a σ G
                 → (subst (liftSubst σ) G) [ a ]
                 ≡ subst (consSubst σ a) G
singleSubstComp a σ G = trans (substCompEq G) (substSingletonComp G)

singleSubstWkComp : ∀ {ρ} a σ G
               → wk (lift ρ) (subst (liftSubst σ) G) [ a ]
               ≡ subst (consSubst (ρ •ₛ σ) a) G
singleSubstWkComp a σ G =
  trans (cong (subst (consSubst var a))
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

singleSubstLift : ∀ {σ} G t
                → subst σ (G [ t ])
                ≡ subst (liftSubst σ) G [ subst σ t ]
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

idWkLiftSubstLemma : ∀ σ G
  → wk (lift (step id)) (subst (liftSubst σ) G) [ var 0 ]
  ≡ subst (liftSubst σ) G
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var zero) σ G)
        (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G)

substVarComp↑ : ∀ {t} σ x
  → (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ zero = refl
substVarComp↑ σ (suc x) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ σ G t
                 → subst (liftSubst σ) (G [ t ]↑)
                 ≡ subst (liftSubst σ) G [ subst (liftSubst σ) t ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVarComp↑ σ) G)))

substConsComp : ∀ {σ t G}
       → subst (consSubst (λ x → σ (suc x)) (subst (tail σ) t)) G
       ≡ subst σ (subst (consSubst (λ x → var (suc x)) (wk1 t)) G)
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { zero → sym (subst-wk t) ; (suc x) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : ∀ F → (wk (lift (step id)) F) [ var zero ] ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) F)
               (subst-id F))

cons-wk-subst : ∀ ρ σ a t
       → subst (consSubst idSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ) t
       ≡ subst (consSubst (ρ •ₛ σ) a) t
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { zero → refl
     ; (suc x) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

natrecSucCaseLemma : ∀ {σ} (x : Nat)
  → (step id •ₛ consSubst (wk1Subst idSubst) (suc (var zero)) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst (liftSubst σ) ₛ• step id ₛ•ₛ consSubst (wk1Subst idSubst) (suc (var zero))) x
natrecSucCaseLemma zero = refl
natrecSucCaseLemma {σ} (suc x) =
  trans (subst-wk (σ x))
           (sym (trans (wk1-wk (step id) _)
                             (wk≡subst (step (step id)) (σ x))))

natrecSucCase : ∀ σ F
  → Term.Π ℕ ▹ (Π subst (liftSubst σ) F
                ▹ subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var zero) ]↑)))
  ≡ Π ℕ ▹ (subst (liftSubst σ) F ▹▹ subst (liftSubst σ) F [ suc (var zero) ]↑)
natrecSucCase σ F =
  cong₂ Π_▹_ refl
    (cong₂ Π_▹_ refl
       (trans (trans (subst-wk (F [ suc (var zero) ]↑))
                           (substCompEq F))
                 (sym (trans (wk-subst (subst (liftSubst σ) F))
                                   (trans (substCompEq F)
                                             (substVar-to-subst natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ F z s m σ (x : Nat)
  → (consSubst idSubst (natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)
     ₛ•ₛ liftSubst (consSubst idSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (λ x → var (suc x)) (suc (var 0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma F z s m σ zero =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma F z s m σ (suc x) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ F z s m σ
  → subst (consSubst σ (suc m)) F
  ≡ subst (liftSubst (consSubst idSubst m))
          (subst (liftSubst (liftSubst σ))
                 (wk1 (F [ suc (var zero) ]↑)))
                   [ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m ]
natrecIrrelevantSubst F z s m σ =
  -- TODO Make nicer
  sym (trans (substCompEq (subst (liftSubst (liftSubst σ))
        (wk (step id)
         (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F))))
         (trans (substCompEq (wk (step id)
        (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F)))
        (trans
           (subst-wk (subst (consSubst (λ x → var (suc x)) (suc (var 0))) F))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma F z s m σ) F)))))

natrecIrrelevantSubstLemma' : ∀ F z s n (x : Nat)
-- TODO Make nicer
  → (consSubst idSubst (natrec F z s n)
     ₛ•ₛ liftSubst (consSubst idSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (λ z₁ → var (suc z₁)) (suc (var zero))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma' F z s n zero =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma' F z s n (suc x) = refl

natrecIrrelevantSubst' : ∀ F z s n →
      subst (liftSubst (consSubst idSubst n))
      (wk1 (F [ suc (var zero) ]↑))
      [ natrec F z s n ]
      ≡
      F [ suc n ]
natrecIrrelevantSubst' F z s n =
  trans (substCompEq (wk (step id)
                              (subst (consSubst (λ x → var (suc x))
                                                (suc (var zero)))
                                     F)))
           (trans (subst-wk (subst (consSubst (λ x → var (suc x))
                                                 (suc (var zero)))
                                      F))
                     (trans (substCompEq F)
                               (substVar-to-subst (natrecIrrelevantSubstLemma' F z s n)
                                        F)))

lemma3 : ∀ {G t σ} →
         subst (consSubst (λ n → σ (suc n)) (subst σ t)) G ≡
         subst σ (subst (consSubst (λ x → var (suc x)) t) G)
lemma3 {G} {t} {σ} = trans (substVar-to-subst
                                (λ { zero → refl
                                ; (suc x) → refl }) G)
                              (sym (substCompEq G))

Geq      : ∀ σ G → subst (consSubst idSubst (var zero))
           (wk (lift (step id)) (subst (liftSubst σ) G))
           ≡ subst (liftSubst σ) G
Geq σ G = trans (subst-wk (subst (liftSubst σ) G))
               (trans (substVar-to-subst (λ { zero → refl ; (suc x) → refl })
                                  (subst (liftSubst σ) G))
                         (subst-id (subst (liftSubst σ) G)))

newlem1 : ∀ {σ t} G → subst
        (λ z → consSubst (λ z₁ → σ z₁) (subst (λ z₁ → σ z₁) t) z) G
        PE.≡ subst σ (subst (consSubst idSubst t) G)
newlem1 G = sym (trans (substCompEq G) (substVar-to-subst (λ { zero → refl ; (suc x) → refl}) G))

substConcatSingleton' : ∀ {a σ} t
                      → subst (σ ₛ•ₛ consSubst idSubst a) t
                      ≡ subst (consSubst σ (subst σ a)) t
substConcatSingleton' t = substVar-to-subst (λ { zero → refl ; (suc x) → refl}) t

wk1-tailId : ∀ t → wk1 t ≡ subst (tail idSubst) t
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)
