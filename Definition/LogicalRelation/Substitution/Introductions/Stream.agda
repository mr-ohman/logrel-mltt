{-# OPTIONS --without-K --safe --guardedness #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Stream {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
import Definition.Typed.Weakening as T
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening as W
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Pi
-- open import Definition.LogicalRelation.MaybeEmbed
open import Definition.LogicalRelation.Irrelevance

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the Str type.
Strᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Str / [Γ]
Strᵛ [Γ] ⊢Δ [σ] = Strᵣ (idRed:*: (Strⱼ ⊢Δ)) , λ [σ′] [σ≡σ′] → id (Strⱼ ⊢Δ)

-- Validity of the Str type as a term.
Strᵗᵛ : ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ Str ∷ U / [Γ] / Uᵛ [Γ]
Strᵗᵛ [Γ] ⊢Δ [σ] =
  let ⊢Str = Strⱼ ⊢Δ
      [Str] = Strᵣ (idRed:*: (Strⱼ ⊢Δ))
      dStr  = idRedTerm:*: ⊢Str
  in
  Uₜ Str dStr Strₙ (≅ₜ-Strrefl ⊢Δ) [Str] ,
  λ [σ′] [σ≡σ′] → Uₜ₌ Str Str dStr dStr Strₙ Strₙ
                  (≅ₜ-Strrefl ⊢Δ) [Str] [Str] (id (Strⱼ ⊢Δ))


hd-subst:*: : ∀ {t t′} → Γ ⊢ t :⇒*: t′ ∷ Str → Γ ⊢ hd t :⇒*: hd t′ ∷ ℕ
hd-subst:*: [ ⊢s , ⊢u , d ] = [ hdⱼ ⊢s ,  hdⱼ ⊢u , hd-subst* d ]

tl-subst:*: : ∀ {t t′} → Γ ⊢ t :⇒*: t′ ∷ Str → Γ ⊢ tl t :⇒*: tl t′ ∷ Str
tl-subst:*: [ ⊢s , ⊢u , d ] = [ tlⱼ ⊢s ,  tlⱼ ⊢u , tl-subst* d ]

redSubst*EqTermℕ : ∀ {t t′ u u′}
                  → Γ ⊢ t :⇒*: t′ ∷ ℕ
                  → Γ ⊢ u :⇒*: u′ ∷ ℕ
                  → Γ ⊩ℕ t′ ≡ u′ ∷ℕ
                  → Γ ⊩ℕ t ≡ u ∷ℕ
redSubst*EqTermℕ t⇒t' u⇒u' (ℕₜ₌ k k′ t'⇒k u'⇒k' k≡k′ prop) =
  ℕₜ₌ k k′ (appendRedTerm:*: t⇒t' t'⇒k)
          (appendRedTerm:*: u⇒u' u'⇒k')
      k≡k′ prop

redSubst*EqTermStr : ∀ {t t′ u u′}
                  → Γ ⊢ t :⇒*: t′ ∷ Str
                  → Γ ⊢ u :⇒*: u′ ∷ Str
                  → Γ ⊩Str t′ ≡ u′ ∷Str
                  → Γ ⊩Str t ≡ u ∷Str
_⊩Str_≡_∷Str.k (redSubst*EqTermStr t⇒t' u⇒u' d) = S≡.k d
_⊩Str_≡_∷Str.k′ (redSubst*EqTermStr t⇒t' u⇒u' d) = S≡.k′ d
_⊩Str_≡_∷Str.d (redSubst*EqTermStr t⇒t' u⇒u' d) =
  appendRedTerm:*: t⇒t' (S≡.d d)
_⊩Str_≡_∷Str.d′ (redSubst*EqTermStr t⇒t' u⇒u' d) =
  appendRedTerm:*: u⇒u' (S≡.d′ d)
_⊩Str_≡_∷Str.k≡k′ (redSubst*EqTermStr t⇒t' u⇒u' d) = S≡.k≡k′ d
_⊩Str_≡_∷Str.prop (redSubst*EqTermStr t⇒t' u⇒u' d) = S≡.prop d



-- Validity of hd.
hdᵛ : ∀ {l s} ([Γ] : ⊩ᵛ Γ) ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ Str / [Γ] / Strᵛ [Γ] )
      → Γ ⊩ᵛ⟨ l ⟩ hd s ∷ ℕ / [Γ] / ℕᵛ [Γ]
hdᵛ {l = l} [Γ] [s] ⊢Δ [σ] =
  let [s] , [s≡s] = [s] ⊢Δ [σ]
      [ℕ] = ℕᵣ {l} (idRed:*: (ℕⱼ ⊢Δ))
      -- [ℕ] = proj₁ (ℕᵛ {l = l} [Γ] ⊢Δ [σ])
      [u] = Sp.hdᵣ (S.prop [s])
      [ _ , _ , d ] = S.d [s]
      [hds] , _ = redSubst*Term (hd-subst* d) [ℕ] [u]
  in [hds] ,
     λ [σ′] [σ≡σ′] →
       let [s≡s′] = [s≡s] [σ′] [σ≡σ′]
           [u≡u′] = S≡p.hdᵣ (S≡.prop [s≡s′])
       in redSubst*EqTermℕ (hd-subst:*: (S≡.d [s≡s′]))
                           (hd-subst:*: (S≡.d′ [s≡s′]))
                           [u≡u′]

-- validity of tl.
tlᵛ : ∀ {l s} ([Γ] : ⊩ᵛ Γ) ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ Str / [Γ] / Strᵛ [Γ] )
      → Γ ⊩ᵛ⟨ l ⟩ tl s ∷ Str / [Γ] / Strᵛ [Γ]
tlᵛ {l = l} [Γ] [s] ⊢Δ [σ] =
  let [s] , [s≡s] = [s] ⊢Δ [σ]
      [Str] = proj₁ (Strᵛ {l = l} [Γ] ⊢Δ [σ])
      [t] = Sp.tlᵣ (S.prop [s])
      [ _ , _ , d ] = S.d [s]
      [tls] , _ = redSubst*Term (tl-subst* d) [Str] [t]
  in [tls] ,
     λ [σ′] [σ≡σ′] →
       let [s≡s′] = [s≡s] [σ′] [σ≡σ′]
           [t≡t′] = S≡p.tlᵣ (S≡.prop [s≡s′])
       in redSubst*EqTermStr (tl-subst:*: (S≡.d [s≡s′]))
                             (tl-subst:*: (S≡.d′ [s≡s′]))
                             [t≡t′]


-- app₀ᵛ : ∀ {F G t u l}
--         ([Γ] : ⊩ᵛ Γ)
--         ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
--         ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
--         ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ F ▹▹ G / [Γ])
--         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F ▹▹ G / [Γ] / [ΠFG])
--         ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
--       → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G / [Γ] / [G]
-- app₀ᵛ {F} {G} {t} {u} {l} [Γ] [F] [G] [ΠFG] [t] [u] =
--   {!!}
--   -- irrelevanceTerm (substSΠ {F = F} {wk1 G} {u} BΠ [Γ] [F] [ΠFG] [u]) [G]



module Coiter {l} {A} {h t : Term _ }
              ([Γ] : ⊩ᵛ Γ)
              ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) where

  [A▹▹ℕ] : _
  [A▹▹ℕ] = ▹▹ᵛ {F = A} {G = ℕ} [Γ] [A] (ℕᵛ [Γ])

  [A▹▹A] : _
  [A▹▹A] = ▹▹ᵛ {F = A} {G = A} [Γ] [A] [A]

  module Helper ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
                ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
                {k} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) where

    [Str] = proj₁ (Strᵛ {l = l} [Γ] ⊢Δ [σ])
    [ℕ] = proj₁ (ℕᵛ {l = l} [Γ] ⊢Δ [σ])

    [A]' = proj₁ ([A] ⊢Δ [σ])
    [h]' = proj₁ ([h] ⊢Δ [σ])
    [t]' = proj₁ ([t] ⊢Δ [σ])

    [A▹▹ℕ]' = proj₁ ([A▹▹ℕ] ⊢Δ [σ])
    [A▹▹A]' = proj₁ ([A▹▹A] ⊢Δ [σ])

    A' = subst σ A
    h' = subst σ h
    t' = subst σ t

    open import Tools.Fin

    aux : ∀ {n m} (σ : Subst n m) x → (liftSubst σ ₛ• step id) x PE.≡ (step id •ₛ σ) x
    aux σ x0 = PE.refl
    aux σ (_+1 x) = PE.refl

    eqA : subst (liftSubst σ) (wk1 A) PE.≡ wk1 (subst σ A)
    eqA = PE.trans (subst-wk A)
          (PE.trans (substVar-to-subst (aux σ) A)
                    (PE.sym (wk-subst A)))

    eqt : Δ ⊢ subst σ (A ▹▹ A) ≡ A' ▹▹ A'
    eqt = PE.subst (λ x → Δ ⊢ subst σ (A ▹▹ A) ≡ Π A' ▹ x)
                   eqA (refl (escape [A▹▹A]'))

    ⊢A' = escape [A]'
    ⊢h' = escapeTerm [A▹▹ℕ]' [h]'
    ⊢t' : Δ ⊢ t' ∷ A' ▹▹ A'
    ⊢t' = conv (escapeTerm [A▹▹A]' [t]') eqt

    A≡A = escapeEq [A]' (reflEq [A]')
    h≡h = escapeTermEq [A▹▹ℕ]' (reflEqTerm [A▹▹ℕ]' [h]')
    t≡t = ≅-conv (escapeTermEq [A▹▹A]' (reflEqTerm [A▹▹A]' [t]')) eqt

    -- s' = subst σ s
    -- [s]' = proj₁ ([s] ⊢Δ [σ])
    mutual
      -- coiter-red : ∀ {s'} ([s]' : Δ ⊩⟨ l ⟩ s' ∷ A' / [A]') → Δ ⊩⟨ l ⟩ coiter A' s' h' t' ∷ Str / [Str]
      coiter-red : ∀ {s₀ s'} (s₀⇒s' : Δ ⊢ s₀ ⇒* coiter A' s' h' t' ∷ Str) ([s]' : Δ ⊩⟨ l ⟩ s' ∷ A' / [A]') → Δ ⊩Str s₀ ∷Str
      _⊩Str_∷Str.n (coiter-red {s₀} {s'} s₀⇒s' [s]') =
        coiter A' s' h' t'
      _⊩Str_∷Str.d (coiter-red {s₀} {s'} s₀⇒s' [s]') =
        let ⊢s' = escapeTerm [A]' [s]'
            ⊢coiter = coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t'
        in -- idRedTerm:*: ⊢coiter
        [ redFirst*Term s₀⇒s' , ⊢coiter , s₀⇒s' ]
      _⊩Str_∷Str.n≡n (coiter-red {s₀} {s'} s₀⇒s' [s]') =
        let s≡s = escapeTermEq [A]' (reflEqTerm [A]' [s]')
        in ≅ₜ-coiter-cong A≡A s≡s h≡h t≡t
      _⊩Str_∷Str.prop (coiter-red {s₀} {s'} s₀⇒s' [s]') = coiter-prop {s'} [s]'

      coiter-prop : ∀ {s'} ([s]' : Δ ⊩⟨ l ⟩ s' ∷ A' / [A]') → Str-prop Δ (coiter A' s' h' t')
      Str-prop.whnf (coiter-prop {s'} [s]') = coiterₙ
      Str-prop.hdᵣ (coiter-prop {s'} [s]') =
        let ⊢s' = escapeTerm [A]' [s]'

            Πₜ h' [ _ , _ , dh' ] funch _ [h≡h]₀ [h]₀ = [h]'
            [hs]₀ = PE.subst (λ x → Δ ⊩ℕ x ∷ℕ) (U.wk-id _) ([h]₀ T.id ⊢Δ (W.wkTerm T.id ⊢Δ [A]' [s]'))
            [hs]₁ , _ = redSubst*Term {l = l} (app-subst* dh' ⊢s') [ℕ] [hs]₀
            [hs] , _ = redSubstTerm (hd-β ⊢A' ⊢s' ⊢h' ⊢t') [ℕ] [hs]₁
        in [hs]
      Str-prop.tlᵣ (coiter-prop {s'} [s]') =
        let ⊢s' = escapeTerm [A]' [s]'

            eqSubst = PE.trans (PE.cong (λ A → A [ s' ]) eqA) (wk1-sgSubst A' s')
            [A]'' = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubst) [A]'

            [Aid] = W.wk T.id ⊢Δ [A]'
            -- (PE.trans (U.wk-id _) eqSubst)
            eqSubst2 = PE.trans (PE.sym (wk-β {a = s'} (subst (liftSubst σ) (wk1 A)))) (wk-id (subst (liftSubst σ) (wk1 A) [ s' ]))

            -- PE.trans (PE.cong (λ A → wk (lift id) A [ wk id s' ]) eqA)
            --            (PE.trans (PE.cong (λ A → A [ wk id s' ]) (lift-wk1 id A')) (wk1-sgSubst A' (wk id s')))

            Πₜ t'' [ _ , _ , dt' ] funct _ [t≡t]₀ [t]₀ = [t]'
            [foo] = (irrelevance′ (PE.sym (singleSubstWkComp {ρ = id} (wk id s') σ (wk1 A)))
                                  (proj₁ (wk1ᵛ {A = A} {F = A} [Γ] [A] [A] ⊢Δ
                                               (consSubstS {A = A} [Γ] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ T.id [σ]) [A]
                                                           (irrelevanceTerm′ (wk-subst A) [Aid]
                                                                             (proj₁ ([A] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ T.id [σ])))
                                                                             (W.wkTerm T.id ⊢Δ [A]' [s]'))))))
            [ts]₀ : Δ ⊩⟨ l ⟩ wk id (t'' ∘ s') ∷ wk (lift id) (subst (liftSubst σ) (wk1 A)) [ wk id s' ] / [foo]
            [ts]₀ = [t]₀ T.id ⊢Δ (W.wkTerm T.id ⊢Δ [A]' [s]')
            [ts]₁ = irrelevanceTerm″ {t = wk id (t'' ∘ s')} {l = l} eqSubst2 (U.wk-id _) [foo] [A]'' [ts]₀
            [ts]₃ , _ = redSubst*Term {l = l} (app-subst* dt' ⊢s') [A]'' [ts]₁
            [ts] = irrelevanceTerm′ eqSubst [A]'' [A]' [ts]₃
            red = tl-β ⊢A' ⊢s' ⊢h' ⊢t' ⇨ id (coiterⱼ ⊢A' (escapeTerm [A]' [ts]) ⊢h' ⊢t')
        in coiter-red {s₀ = tl (coiter A' s' h' t')} {s' = t' ∘ s'} red [ts]



  coiterᵛ :  ∀ {s}
            ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
            ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
          → Γ ⊩ᵛ⟨ l ⟩ coiter A s h t ∷ Str / [Γ] / Strᵛ [Γ]
  coiterᵛ {s} [s] [h] [t] {σ = σ} ⊢Δ [σ] =
    let [s]' , _ = [s] ⊢Δ [σ]
        s' = subst σ s
        ⊢s' = escapeTerm [A]' [s]'
    in
    coiter-red (id (coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t')) [s]'  ,
    {!!}
    where
      open Helper [h] [t] ⊢Δ [σ]
