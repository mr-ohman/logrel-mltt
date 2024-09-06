{-# OPTIONS --without-K --safe #-}

module Definition.Untyped.Properties where

open import Definition.Untyped
open import Flex.Untyped.Properties public

open import Tools.Fin
open import Tools.Nat
open import Tools.List
open import Tools.PropositionalEquality hiding (subst)

private
  variable
    ℓ m n : Nat
    ρ ρ′ : Wk m n
    η : Wk n ℓ
    σ σ′ : Subst m n

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ (ρ : Wk m n) G
  → Π ℕ ▹ (Π wk (lift ρ) G ▹ wk (lift (lift ρ)) (wk1 (G [ suc (var x0) ]↑)))
  ≡ Π ℕ ▹ (wk (lift ρ) G ▹▹ wk (lift ρ) G [ suc (var x0) ]↑)
wk-β-natrec ρ G =
  cong₂ Π_▹_ refl (cong₂ Π_▹_ refl
    (trans (wk-comp (lift (lift ρ)) (step id)
                    (subst (consSubst (wk1Subst var) (suc (var x0))) G))
       (trans (wk-subst G) (sym (trans (wk-subst (wk (lift ρ) G))
         (trans (subst-wk G)
                (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)))))))

natrecSucCaseLemma : (x : Fin (1+ n))
  → (step id •ₛ consSubst (wk1Subst idSubst) (suc (var x0)) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst (liftSubst σ) ₛ• step id ₛ•ₛ consSubst (wk1Subst idSubst) (suc (var x0))) x
natrecSucCaseLemma x0 = refl
natrecSucCaseLemma {σ = σ} (x +1) =
  trans (subst-wk (σ x))
           (sym (trans (wk1-wk (step id) _)
                             (wk≡subst (step (step id)) (σ x))))

natrecSucCase : ∀ (σ : Subst m n) F
  → Π ℕ ▹ (Π subst (liftSubst σ) F
                ▹ subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var x0) ]↑)))
  ≡ Π ℕ ▹ (subst (liftSubst σ) F ▹▹ subst (liftSubst σ) F [ suc (var x0) ]↑)
natrecSucCase σ F =
  cong₂ Π_▹_ refl
    (cong₂ Π_▹_ refl
       (trans (trans (subst-wk (F [ suc (var x0) ]↑))
                           (substCompEq F))
                 (sym (trans (wk-subst (subst (liftSubst σ) F))
                                   (trans (substCompEq F)
                                             (substVar-to-subst natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ F z s m (σ : Subst ℓ n) (x : Fin (1+ n))
  → (sgSubst (natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma F z s m σ x0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma F z s m σ (x +1) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ F z s m (σ : Subst ℓ n)
  → subst (consSubst σ (suc m)) F
  ≡ subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
                 (wk1 (F [ suc (var x0) ]↑)))
                   [ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m ]
natrecIrrelevantSubst F z s m σ =
  sym (trans (substCompEq (subst (liftSubst (liftSubst σ))
        (wk (step id)
         (subst (consSubst (tail idSubst) (suc (var x0))) F))))
         (trans (substCompEq (wk (step id)
        (subst (consSubst (tail idSubst) (suc (var x0))) F)))
        (trans
           (subst-wk (subst (consSubst (tail idSubst) (suc (var x0))) F))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ F z s n (x : Fin (1+ m))
  → (sgSubst (natrec F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ F z s n x0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ F z s n (x +1) = refl

natrecIrrelevantSubst′ : ∀ (F : Term (1+ m)) z s n
  → subst (liftSubst (sgSubst n))
      (wk1 (F [ suc (var x0) ]↑))
      [ natrec F z s n ]
  ≡ F [ suc n ]
natrecIrrelevantSubst′ F z s n =
  trans (substCompEq (wk (step id)
                         (subst (consSubst (tail idSubst) (suc (var x0))) F)))
        (trans (subst-wk (subst (consSubst (tail idSubst) (suc (var x0))) F))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ F z s n) F)))

