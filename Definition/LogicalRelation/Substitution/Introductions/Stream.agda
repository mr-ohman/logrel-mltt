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
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Reduction
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

hd-congᵛ : ∀ {l s s'}
           ([Γ] : ⊩ᵛ Γ)
           ([s≡s'] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s' ∷ Str / [Γ] / Strᵛ [Γ])
         → Γ ⊩ᵛ⟨ l ⟩ hd s ≡ hd s' ∷ ℕ / [Γ] / ℕᵛ [Γ]
hd-congᵛ {l = l} {s} {s'} [Γ] [s≡s'] {σ} ⊢Δ [σ] =
  let w = [s≡s'] ⊢Δ [σ]
  in redSubst*EqTermℕ (hd-subst:*: (w .S≡.d)) (hd-subst:*: (w .S≡.d′)) (w .S≡.prop .S≡p.hdᵣ)


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

tl-congᵛ : ∀ {l s s'}
           ([Γ] : ⊩ᵛ Γ)
           ([s≡s'] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s' ∷ Str / [Γ] / Strᵛ [Γ])
         → Γ ⊩ᵛ⟨ l ⟩ tl s ≡ tl s' ∷ Str / [Γ] / Strᵛ [Γ]
tl-congᵛ {l = l} {s} {s'} [Γ] [s≡s'] {σ} ⊢Δ [σ] =
  let w = [s≡s'] ⊢Δ [σ]
  in redSubst*EqTermStr (tl-subst:*: (w .S≡.d)) (tl-subst:*: (w .S≡.d′)) (w .S≡.prop .S≡p.tlᵣ)






subst-▹▹ : ∀ {l k n} (A : Term n) {Δ} (σ : _ → Term k) ([A▹▹A] : Δ ⊩⟨ l ⟩ subst σ (A ▹▹ A)) →  Δ ⊢ subst σ (A ▹▹ A) ≡ subst σ A ▹▹ subst σ A
subst-▹▹ A {Δ} σ [A▹▹A] = PE.subst (λ x → Δ ⊢ subst σ (A ▹▹ A) ≡ Π subst σ A ▹ x)
                               (subst-liftSubst-wk1 A σ) (refl (escape [A▹▹A]))


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

    eqA = subst-liftSubst-wk1 A σ

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
            [hs]₁ = appTerm [A]' [ℕ] [A▹▹ℕ]' [h]' [s]'
            [hs] , _ = redSubstTerm (hd-β ⊢A' ⊢s' ⊢h' ⊢t') [ℕ] [hs]₁
        in [hs]
      Str-prop.tlᵣ (coiter-prop {s'} [s]') =
        let ⊢s' = escapeTerm [A]' [s]'

            eqSubst = PE.trans (PE.cong (λ A → A [ s' ]) eqA) (wk1-sgSubst A' s')
            [A]'' = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubst) [A]'

            [ts]₀ = appTerm [A]' [A]'' [A▹▹A]' [t]' [s]'
            [ts] = irrelevanceTerm′ eqSubst [A]'' [A]' [ts]₀
            red = tl-β ⊢A' ⊢s' ⊢h' ⊢t' ⇨ id (coiterⱼ ⊢A' (escapeTerm [A]' [ts]) ⊢h' ⊢t')
        in coiter-red {s₀ = tl (coiter A' s' h' t')} {s' = t' ∘ s'} red [ts]


    module HelperExt {σ'} ([σ'] : Δ ⊩ˢ σ' ∷ Γ / [Γ] / ⊢Δ) ([σ≡σ'] : Δ ⊩ˢ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]) where

      A'' = subst σ' A
      h'' = subst σ' h
      t'' = subst σ' t

      [A]'' = proj₁ ([A] ⊢Δ [σ'])
      [h]'' = proj₁ ([h] ⊢Δ [σ'])
      [t]'' = proj₁ ([t] ⊢Δ [σ'])

      [A▹▹ℕ]'' = proj₁ ([A▹▹ℕ] ⊢Δ [σ'])
      [A▹▹A]'' = proj₁ ([A▹▹A] ⊢Δ [σ'])

      [A'≡A''] = proj₂ ([A] ⊢Δ [σ]) [σ'] [σ≡σ']
      [h'≡h''] = proj₂ ([h] ⊢Δ [σ]) [σ'] [σ≡σ']
      [t'≡t''] = proj₂ ([t] ⊢Δ [σ]) [σ'] [σ≡σ']

      eqt' : Δ ⊢ subst σ' (A ▹▹ A) ≡ A'' ▹▹ A''
      eqt' = PE.subst (λ x → Δ ⊢ subst σ' (A ▹▹ A) ≡ Π A'' ▹ x)
                    (subst-liftSubst-wk1 A σ') (refl (escape [A▹▹A]''))

      ⊢A'' = escape [A]''
      ⊢h'' = escapeTerm [A▹▹ℕ]'' [h]''
      ⊢t'' : Δ ⊢ t'' ∷ A'' ▹▹ A''
      ⊢t'' = conv (escapeTerm [A▹▹A]'' [t]'') eqt'

      mutual
        coiter-red-ext : ∀ {s₀ s₀' s' s''}
                        (s₀⇒s' : Δ ⊢ s₀ ⇒* coiter A' s' h' t' ∷ Str)
                        (s₀'⇒s'' : Δ ⊢ s₀' ⇒* coiter A'' s'' h'' t'' ∷ Str)
                        ([s]' : Δ ⊩⟨ l ⟩ s' ∷ A' / [A]')
                        ([s]'' : Δ ⊩⟨ l ⟩ s'' ∷ A'' / [A]'')
                        ([s'≡s''] : Δ ⊩⟨ l ⟩ s' ≡ s'' ∷ A' / [A]')
                      → Δ ⊩Str s₀ ≡ s₀' ∷Str
        _⊩Str_≡_∷Str.k (coiter-red-ext {s' = s'} s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) = coiter A' s' h' t'
        _⊩Str_≡_∷Str.k′ (coiter-red-ext {s'' = s''} s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) = coiter A'' s'' h'' t''
        _⊩Str_≡_∷Str.d (coiter-red-ext s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) =
          let ⊢s' = escapeTerm [A]' [s]'
              ⊢coiter = coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t'
          in [ redFirst*Term s₀⇒s' , ⊢coiter , s₀⇒s' ]
        _⊩Str_≡_∷Str.d′ (coiter-red-ext s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) =
          let ⊢s'' = escapeTerm [A]'' [s]''
              ⊢coiter' = coiterⱼ ⊢A'' ⊢s'' ⊢h'' ⊢t''
          in [ redFirst*Term s₀'⇒s'' , ⊢coiter' , s₀'⇒s'' ]
        _⊩Str_≡_∷Str.k≡k′ (coiter-red-ext s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) =
          ≅ₜ-coiter-cong (escapeEq [A]' [A'≡A''])
                         (escapeTermEq [A]' [s'≡s''])
                         (escapeTermEq [A▹▹ℕ]' [h'≡h''])
                         (PE.subst (λ x → Δ ⊢ t' ≅ t'' ∷ Π A' ▹ x) eqA (escapeTermEq [A▹▹A]' [t'≡t'']))
        _⊩Str_≡_∷Str.prop (coiter-red-ext s₀⇒s' s₀'⇒s'' [s]' [s]'' [s'≡s'']) = coiter-prop-ext [s]' [s]'' [s'≡s'']

        coiter-prop-ext : ∀ {s' s''}
                          ([s]' : Δ ⊩⟨ l ⟩ s' ∷ A' / [A]')
                          ([s]'' : Δ ⊩⟨ l ⟩ s'' ∷ A'' / [A]'')
                          ([s'≡s''] : Δ ⊩⟨ l ⟩ s' ≡ s'' ∷ A' / [A]')
                        → [Str]-prop Δ (coiter A' s' h' t') (coiter A'' s'' h'' t'')
        [Str]-prop.whnf (coiter-prop-ext [s]' [s]'' [s'≡s'']) = coiterₙ
        [Str]-prop.whnf′ (coiter-prop-ext [s]' [s]'' [s'≡s'']) = coiterₙ
        [Str]-prop.hdᵣ (coiter-prop-ext [s]' [s]'' [s'≡s'']) =
          let ⊢s' = escapeTerm [A]' [s]'
              ⊢s'' = escapeTerm [A]'' [s]''
              ⊢coiter = coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t'
              ⊢coiter' = coiterⱼ ⊢A'' ⊢s'' ⊢h'' ⊢t''
              ⊢hs = ⊢h' ∘ⱼ ⊢s'
              ⊢hs' = ⊢h'' ∘ⱼ ⊢s''

              [hs'≡hs''] = app-congTerm [A]' [ℕ] [A▹▹ℕ]' [h'≡h''] [s]' (convTerm₂ [A]' [A]'' [A'≡A''] [s]'') [s'≡s'']
              red' = [ hdⱼ ⊢coiter , ⊢hs , hd-β ⊢A' ⊢s' ⊢h' ⊢t' ⇨ id ⊢hs ]
              red'' = [ hdⱼ ⊢coiter' , ⊢hs' , hd-β ⊢A'' ⊢s'' ⊢h'' ⊢t'' ⇨ id ⊢hs' ]
          in redSubst*EqTermℕ red' red'' [hs'≡hs'']
        [Str]-prop.tlᵣ (coiter-prop-ext {s' = s'} {s'' = s''} [s]' [s]'' [s'≡s'']) =
          let ⊢s' = escapeTerm [A]' [s]'
              ⊢s'' = escapeTerm [A]'' [s]''

              eqSubst = PE.trans (PE.cong (λ A → A [ s' ]) eqA) (wk1-sgSubst A' s')
              wk[A]' = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubst) [A]'
              eqSubst' = PE.trans (PE.cong (λ A → A [ s'' ]) (subst-liftSubst-wk1 A σ')) (wk1-sgSubst A'' s'')
              wk[A]'' = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubst') [A]''

              [ts']₀ = appTerm [A]' wk[A]' [A▹▹A]' [t]' [s]'
              [ts'] = irrelevanceTerm′ eqSubst wk[A]' [A]' [ts']₀

              [ts'']₀ = appTerm [A]'' wk[A]'' [A▹▹A]'' [t]'' [s]''
              [ts''] = irrelevanceTerm′ eqSubst' wk[A]'' [A]'' [ts'']₀

              [ts'≡ts'']₀ = app-congTerm [A]' wk[A]' [A▹▹A]' [t'≡t''] [s]' (convTerm₂ [A]' [A]'' [A'≡A''] [s]'') [s'≡s'']
              [ts'≡ts''] = irrelevanceEqTerm′ eqSubst wk[A]' [A]' [ts'≡ts'']₀

              red' = tl-β ⊢A' ⊢s' ⊢h' ⊢t' ⇨ id (coiterⱼ ⊢A' (escapeTerm [A]' [ts']) ⊢h' ⊢t')
              red'' = tl-β ⊢A'' ⊢s'' ⊢h'' ⊢t'' ⇨ id (coiterⱼ ⊢A'' (escapeTerm [A]'' [ts'']) ⊢h'' ⊢t'')
          in coiter-red-ext red' red'' [ts']  [ts'']  [ts'≡ts'']

      coiter-red-ext′ : ∀ {s} ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A]) → Δ ⊩Str coiter A' (subst σ s) h' t' ≡ coiter A'' (subst σ' s) h'' t'' ∷Str
      coiter-red-ext′ {s} [s] =
        let [s]' , [s'≡s''] = [s] ⊢Δ [σ]
            s' = subst σ s
            ⊢s' = escapeTerm [A]' [s]'
            ⊢coiter = coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t'
            [s]'' , _ = [s] ⊢Δ [σ']
            s'' = subst σ' s
            ⊢s'' = escapeTerm [A]'' [s]''
            ⊢coiter' = coiterⱼ ⊢A'' ⊢s'' ⊢h'' ⊢t''
        in
        coiter-red-ext (id ⊢coiter) (id ⊢coiter') [s]' [s]'' ([s'≡s''] [σ'] [σ≡σ'])

  coiterᵛ :  ∀ {s}
            ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
            ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
          → Γ ⊩ᵛ⟨ l ⟩ coiter A s h t ∷ Str / [Γ] / Strᵛ [Γ]
  coiterᵛ {s} [s] [h] [t] {σ = σ} ⊢Δ [σ] =
    let [s]' , [s'≡s''] = [s] ⊢Δ [σ]
        s' = subst σ s
        ⊢s' = escapeTerm [A]' [s]'
        ⊢coiter = coiterⱼ ⊢A' ⊢s' ⊢h' ⊢t'
    in
    coiter-red (id ⊢coiter) [s]' ,
    λ {σ'} [σ'] [σ≡σ'] → HelperExt.coiter-red-ext′ [σ'] [σ≡σ'] {s} [s]
    where
      open Helper [h] [t] ⊢Δ [σ]

open Coiter public using (coiterᵛ)


module CoiterCongTerm {l A A' h h' t t'}
                      ([Γ] : ⊩ᵛ Γ)
                      ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
                      ([A'] : Γ ⊩ᵛ⟨ l ⟩ A' / [Γ])
                      ([A▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ ℕ / [Γ])
                      ([A'▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A' ▹▹ ℕ / [Γ])
                      ([A▹▹A] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ A / [Γ])
                      ([A'▹▹A'] : Γ ⊩ᵛ⟨ l ⟩ A' ▹▹ A' / [Γ])
                      ([A≡A'] : Γ ⊩ᵛ⟨ l ⟩ A ≡ A' / [Γ] / [A])
                      ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
                      ([h'] : Γ ⊩ᵛ⟨ l ⟩ h' ∷ A' ▹▹ ℕ / [Γ] / [A'▹▹ℕ])
                      ([h≡h'] : Γ ⊩ᵛ⟨ l ⟩ h ≡ h' ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
                      ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
                      ([t'] : Γ ⊩ᵛ⟨ l ⟩ t' ∷ A' ▹▹ A' / [Γ] / [A'▹▹A'])
                      ([t≡t'] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t' ∷ A ▹▹ A / [Γ] / [A▹▹A])
                      {k} {Δ : Con Term k} {σ} {σ'} (⊢Δ : ⊢ Δ)
                      ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                      ([σ'] : Δ ⊩ˢ σ' ∷ Γ / [Γ] / ⊢Δ)
                      ([σ≡σ'] : Δ ⊩ˢ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ])
                      where


  Aσ = subst σ A
  Aσ' = subst σ' A'
  hσ = subst σ h
  hσ' = subst σ' h'
  tσ = subst σ t
  tσ' = subst σ' t'

  [Aσ] = proj₁ ([A] ⊢Δ [σ])
  [Aσ'] = proj₁ ([A'] ⊢Δ [σ'])
  [A'σ≡A'σ'] = proj₂ ([A'] ⊢Δ [σ]) [σ'] [σ≡σ']

  [A▹▹ℕσ] = proj₁ ([A▹▹ℕ] ⊢Δ [σ])
  [A▹▹ℕσ'] = proj₁ ([A'▹▹ℕ] ⊢Δ [σ'])
  [A'▹▹ℕσ] = proj₁ ([A'▹▹ℕ] ⊢Δ [σ])
  [A'▹▹ℕσ≡A'▹▹ℕσ'] = proj₂ ([A'▹▹ℕ] ⊢Δ [σ]) [σ'] [σ≡σ']

  [A▹▹Aσ] = proj₁ ([A▹▹A] ⊢Δ [σ])
  [A▹▹Aσ'] = proj₁ ([A'▹▹A'] ⊢Δ [σ'])
  [A'▹▹A'σ] = proj₁ ([A'▹▹A'] ⊢Δ [σ])
  [A'▹▹A'σ≡A'▹▹A'σ'] = proj₂ ([A'▹▹A'] ⊢Δ [σ]) [σ'] [σ≡σ']

  [A≡A'σ] = [A≡A'] ⊢Δ [σ]

  [hσ] = proj₁ ([h] ⊢Δ [σ])
  [hσ'] = proj₁ ([h'] ⊢Δ [σ'])
  [h≡h'σ] = [h≡h'] ⊢Δ [σ]

  [tσ] = proj₁ ([t] ⊢Δ [σ])
  [tσ'] = proj₁ ([t'] ⊢Δ [σ'])
  [t≡t'σ] = [t≡t'] ⊢Δ [σ]

  eqt : Δ ⊢ subst σ (A ▹▹ A) ≡ Aσ ▹▹ Aσ
  eqt = PE.subst (λ x → Δ ⊢ subst σ (A ▹▹ A) ≡ Π Aσ ▹ x)
                (subst-liftSubst-wk1 A σ) (refl (escape [A▹▹Aσ]))

  ⊢Aσ = escape [Aσ]
  ⊢hσ = escapeTerm [A▹▹ℕσ] [hσ]
  ⊢tσ : Δ ⊢ tσ ∷ Aσ ▹▹ Aσ
  ⊢tσ = conv (escapeTerm [A▹▹Aσ] [tσ]) eqt

  eqt' : Δ ⊢ subst σ' (A' ▹▹ A') ≡ Aσ' ▹▹ Aσ'
  eqt' = PE.subst (λ x → Δ ⊢ subst σ' (A' ▹▹ A') ≡ Π Aσ' ▹ x)
                (subst-liftSubst-wk1 A' σ') (refl (escape [A▹▹Aσ']))

  ⊢Aσ' = escape [Aσ']
  ⊢hσ' = escapeTerm [A▹▹ℕσ'] [hσ']
  ⊢tσ' : Δ ⊢ tσ' ∷ Aσ' ▹▹ Aσ'
  ⊢tσ' = conv (escapeTerm [A▹▹Aσ'] [tσ']) eqt'


  [Aσ≡A'σ'] = transEq [Aσ] (proj₁ ([A'] ⊢Δ [σ])) [Aσ'] [A≡A'σ] [A'σ≡A'σ']

  [A▹▹ℕσ≡A'▹▹ℕσ] = irrelevanceEq (proj₁ (ndᵛ {F = A} {G = ℕ} BΠ [Γ] [A] (ℕᵛ [Γ]) ⊢Δ [σ])) [A▹▹ℕσ]
                 (▹▹-congᵛ {F = A} {F′ = A'} {G = ℕ} {G′ = ℕ}  [Γ] [A] [A'] [A≡A'] (ℕᵛ [Γ]) (ℕᵛ [Γ]) (reflᵛ {A = ℕ} {l = l} [Γ] (ℕᵛ [Γ])) ⊢Δ [σ])

  [A▹▹Aσ≡A'▹▹A'σ] = irrelevanceEq (proj₁ (ndᵛ {F = A} {G = A} BΠ [Γ] [A] [A] ⊢Δ [σ])) [A▹▹Aσ]
                                   (▹▹-congᵛ {F = A} {F′ = A'} {G = A} {G′ = A'}  [Γ] [A] [A'] [A≡A'] [A] [A'] [A≡A'] ⊢Δ [σ])

  [h'σ≡h'σ'] = convEqTerm₂ [A▹▹ℕσ] [A'▹▹ℕσ] [A▹▹ℕσ≡A'▹▹ℕσ] (proj₂ ([h'] ⊢Δ [σ]) [σ'] [σ≡σ'])
  [hσ≡h'σ'] = transEqTerm [A▹▹ℕσ] [h≡h'σ] [h'σ≡h'σ']

  [t'σ≡t'σ'] = convEqTerm₂ [A▹▹Aσ] [A'▹▹A'σ] [A▹▹Aσ≡A'▹▹A'σ] (proj₂ ([t'] ⊢Δ [σ]) [σ'] [σ≡σ'])
  [tσ≡t'σ'] = transEqTerm [A▹▹Aσ] [t≡t'σ] [t'σ≡t'σ']

  ⊢Aσ≡A'σ' = escapeEq [Aσ] [Aσ≡A'σ']
  ⊢hσ≡h'σ' = escapeTermEq [A▹▹ℕσ] [hσ≡h'σ']
  ⊢tσ≡t'σ' = escapeTermEq [A▹▹Aσ] [tσ≡t'σ']

  [ℕ] = proj₁ (ℕᵛ {l = l} [Γ] ⊢Δ [σ])

  mutual
    coiter-cong-red : ∀ {s₀ s₀' s₁ s₁'}
                        (s₀⇒s₁ : Δ ⊢ s₀ ⇒* coiter Aσ s₁ hσ tσ ∷ Str)
                        (s₀'⇒s₁' : Δ ⊢ s₀' ⇒* coiter Aσ' s₁' hσ' tσ' ∷ Str)
                        ([s₁] : Δ ⊩⟨ l ⟩ s₁ ∷ Aσ / [Aσ])
                        ([s₁'] : Δ ⊩⟨ l ⟩ s₁' ∷ Aσ' / [Aσ'])
                        ([s₁≡s₁'] : Δ ⊩⟨ l ⟩ s₁ ≡ s₁' ∷ Aσ / [Aσ])
                    → Δ ⊩Str s₀ ≡ s₀' ∷Str
    _⊩Str_≡_∷Str.k (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      coiter Aσ s₁ hσ tσ
    _⊩Str_≡_∷Str.k′ (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      coiter Aσ' s₁' hσ' tσ'
    _⊩Str_≡_∷Str.d (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      let ⊢s₁ = escapeTerm [Aσ] [s₁]
          ⊢coiter =  coiterⱼ ⊢Aσ ⊢s₁ ⊢hσ ⊢tσ
      in [ redFirst*Term s₀⇒s₁ , ⊢coiter , s₀⇒s₁ ]
    _⊩Str_≡_∷Str.d′ (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      let ⊢s₁' = escapeTerm [Aσ'] [s₁']
          ⊢coiter' =  coiterⱼ ⊢Aσ' ⊢s₁' ⊢hσ' ⊢tσ'
      in [ redFirst*Term s₀'⇒s₁' , ⊢coiter' , s₀'⇒s₁' ]
    _⊩Str_≡_∷Str.k≡k′ (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      ≅ₜ-coiter-cong ⊢Aσ≡A'σ' (escapeTermEq [Aσ] [s₁≡s₁']) ⊢hσ≡h'σ' (≅-conv ⊢tσ≡t'σ' eqt)
    _⊩Str_≡_∷Str.prop (coiter-cong-red {s₀} {s₀'} {s₁} {s₁'} s₀⇒s₁ s₀'⇒s₁' [s₁] [s₁'] [s₁≡s₁']) =
      coiter-cong-prop [s₁] [s₁'] [s₁≡s₁']

    --coiter A'σ s₁' h'σ t'σ

    coiter-cong-prop : ∀ {s₁ s₁'}
                        ([s₁] : Δ ⊩⟨ l ⟩ s₁ ∷ Aσ / [Aσ])
                        ([s₁'] : Δ ⊩⟨ l ⟩ s₁' ∷ Aσ' / [Aσ'])
                        ([s₁≡s₁'] : Δ ⊩⟨ l ⟩ s₁ ≡ s₁' ∷ Aσ / [Aσ])
                    → [Str]-prop Δ (coiter Aσ s₁ hσ tσ) (coiter Aσ' s₁' hσ' tσ')
    [Str]-prop.whnf (coiter-cong-prop {s₁} {s₁'} [s₁] [s₁'] [s₁≡s₁']) = coiterₙ
    [Str]-prop.whnf′ (coiter-cong-prop {s₁} {s₁'} [s₁] [s₁'] [s₁≡s₁']) = coiterₙ
    [Str]-prop.hdᵣ (coiter-cong-prop {s₁} {s₁'} [s₁] [s₁'] [s₁≡s₁']) =
      let ⊢s₁ = escapeTerm [Aσ] [s₁]
          ⊢s₁' = escapeTerm [Aσ'] [s₁']
          ⊢coiter = coiterⱼ ⊢Aσ ⊢s₁ ⊢hσ ⊢tσ
          ⊢coiter' = coiterⱼ ⊢Aσ' ⊢s₁' ⊢hσ' ⊢tσ'
          ⊢hs = ⊢hσ ∘ⱼ ⊢s₁
          ⊢hs' = ⊢hσ' ∘ⱼ ⊢s₁'

          [hs₁≡hs₁'] = app-congTerm [Aσ] [ℕ] [A▹▹ℕσ] [hσ≡h'σ'] [s₁] (convTerm₂ [Aσ] [Aσ'] [Aσ≡A'σ'] [s₁']) [s₁≡s₁']
          red = [ hdⱼ ⊢coiter , ⊢hs , hd-β ⊢Aσ ⊢s₁ ⊢hσ ⊢tσ ⇨ id ⊢hs ]
          red' = [ hdⱼ ⊢coiter' , ⊢hs' , hd-β ⊢Aσ' ⊢s₁' ⊢hσ' ⊢tσ' ⇨ id ⊢hs' ]
      in redSubst*EqTermℕ red red' [hs₁≡hs₁']
    [Str]-prop.tlᵣ (coiter-cong-prop {s₁} {s₁'} [s₁] [s₁'] [s₁≡s₁']) =
      let ⊢s₁ = escapeTerm [Aσ] [s₁]
          ⊢s₁' = escapeTerm [Aσ'] [s₁']

          eqSubst = PE.trans (PE.cong (λ A → A [ s₁ ]) (subst-liftSubst-wk1 A σ)) (wk1-sgSubst Aσ s₁)
          wk[Aσ] = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubst) [Aσ]
          eqSubstσ = PE.trans (PE.cong (λ A → A [ s₁' ]) (subst-liftSubst-wk1 A' σ')) (wk1-sgSubst Aσ' s₁')
          wk[Aσ'] = PE.subst (λ A → Δ ⊩⟨ l ⟩ A) (PE.sym eqSubstσ) [Aσ']

          [ts₁]₀ = appTerm [Aσ] wk[Aσ] [A▹▹Aσ] [tσ] [s₁]
          [ts₁] = irrelevanceTerm′ eqSubst wk[Aσ] [Aσ] [ts₁]₀

          [ts₁']₀ = appTerm [Aσ'] wk[Aσ'] [A▹▹Aσ'] [tσ'] [s₁']
          [ts₁'] = irrelevanceTerm′ eqSubstσ wk[Aσ'] [Aσ'] [ts₁']₀

          [ts₁≡ts₁']₀ = app-congTerm [Aσ] wk[Aσ] [A▹▹Aσ] [tσ≡t'σ'] [s₁] (convTerm₂ [Aσ] [Aσ'] [Aσ≡A'σ'] [s₁']) [s₁≡s₁']
          [ts₁≡ts₁'] = irrelevanceEqTerm′ eqSubst wk[Aσ] [Aσ] [ts₁≡ts₁']₀

          red' = tl-β ⊢Aσ ⊢s₁ ⊢hσ ⊢tσ ⇨ id (coiterⱼ ⊢Aσ (escapeTerm [Aσ] [ts₁]) ⊢hσ ⊢tσ)
          red'' = tl-β ⊢Aσ' ⊢s₁' ⊢hσ' ⊢tσ' ⇨ id (coiterⱼ ⊢Aσ' (escapeTerm [Aσ'] [ts₁']) ⊢hσ' ⊢tσ')
      in coiter-cong-red red' red'' [ts₁]  [ts₁']  [ts₁≡ts₁']


  coiter-cong-red′ : ∀ {s s'}
                       ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
                       ([s'] : Γ ⊩ᵛ⟨ l ⟩ s' ∷ A' / [Γ] / [A'])
                       ([s≡s'] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s' ∷ A / [Γ] / [A])
                     → Δ ⊩Str coiter Aσ (subst σ s) hσ tσ ≡ coiter Aσ' (subst σ' s') hσ' tσ' ∷Str
  coiter-cong-red′ {s} {s'} [s] [s'] [s≡s'] =
    let [s₁] , [s₁≡s₁'] = [s] ⊢Δ [σ]
        s₁ = subst σ s
        ⊢s₁ = escapeTerm [Aσ] [s₁]
        ⊢coiter = coiterⱼ ⊢Aσ ⊢s₁ ⊢hσ ⊢tσ
        [s₁'] , _ = [s'] ⊢Δ [σ']
        s₁' = subst σ' s'
        ⊢s₁' = escapeTerm [Aσ'] [s₁']
        ⊢coiter' = coiterⱼ ⊢Aσ' ⊢s₁' ⊢hσ' ⊢tσ'
    in
    coiter-cong-red (id ⊢coiter) (id ⊢coiter') [s₁] [s₁']
                    (transEqTerm [Aσ] ([s₁≡s₁'] [σ'] [σ≡σ']) (convEqTerm₂ [Aσ] (proj₁ ([A] ⊢Δ [σ'])) (proj₂ ([A] ⊢Δ [σ]) [σ'] [σ≡σ']) ([s≡s'] ⊢Δ [σ']) ) )

coiter-congᵛ : ∀ {l A A' s s' h h' t t'}
                ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
                ([A'] : Γ ⊩ᵛ⟨ l ⟩ A' / [Γ])
                ([A▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ ℕ / [Γ])
                ([A'▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A' ▹▹ ℕ / [Γ])
                ([A▹▹A] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ A / [Γ])
                ([A'▹▹A'] : Γ ⊩ᵛ⟨ l ⟩ A' ▹▹ A' / [Γ])
                ([A≡A'] : Γ ⊩ᵛ⟨ l ⟩ A ≡ A' / [Γ] / [A])
                ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
                ([s'] : Γ ⊩ᵛ⟨ l ⟩ s' ∷ A' / [Γ] / [A'])
                ([s≡s'] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s' ∷ A / [Γ] / [A])
                ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
                ([h'] : Γ ⊩ᵛ⟨ l ⟩ h' ∷ A' ▹▹ ℕ / [Γ] / [A'▹▹ℕ])
                ([h≡h'] : Γ ⊩ᵛ⟨ l ⟩ h ≡ h' ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
                ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
                ([t'] : Γ ⊩ᵛ⟨ l ⟩ t' ∷ A' ▹▹ A' / [Γ] / [A'▹▹A'])
                ([t≡t'] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t' ∷ A ▹▹ A / [Γ] / [A▹▹A])
             → Γ ⊩ᵛ⟨ l ⟩ coiter A s h t ≡ coiter A' s' h' t' ∷ Str / [Γ] / Strᵛ [Γ]
coiter-congᵛ {l = l} {A} {A'} {s} {s'} {h} {h'} {t} {t'} [Γ] [A] [A'] [A▹▹ℕ] [A'▹▹ℕ] [A▹▹A] [A'▹▹A'] [A≡A'] [s] [s'] [s≡s'] [h] [h'] [h≡h'] [t] [t'] [t≡t'] {k} {Δ} {σ} ⊢Δ [σ] =
   coiter-cong-red′ {s = s} {s' = s'} [s] [s'] [s≡s']
  where
    open CoiterCongTerm {l = l} {A} {A'} {h} {h'} {t} {t'} [Γ] [A] [A'] [A▹▹ℕ] [A'▹▹ℕ] [A▹▹A] [A'▹▹A'] [A≡A'] [h] [h'] [h≡h'] [t] [t'] [t≡t'] ⊢Δ [σ] [σ] (reflSubst [Γ] ⊢Δ [σ])



hd-βᵛ : ∀ {l A s h t}
        ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([A▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ ℕ / [Γ])
        ([A▹▹A] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ A / [Γ])
        ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
        ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
      → Γ ⊩ᵛ⟨ l ⟩ hd (coiter A s h t) ≡ h ∘ s ∷ ℕ / [Γ] / ℕᵛ [Γ]
hd-βᵛ {l = l} {A} {s} {h} {t} [Γ] [A] [A▹▹ℕ] [A▹▹A] [s] [h] [t] {σ = σ} ⊢Δ [σ] =
  let [ℕ] = proj₁ (ℕᵛ {l = l} [Γ] ⊢Δ [σ])
      [A]' = proj₁ ([A] ⊢Δ [σ])
      [A▹▹ℕ]' = proj₁ ([A▹▹ℕ] ⊢Δ [σ])
      [A▹▹A]' = proj₁ ([A▹▹A] ⊢Δ [σ])
      [s]' = proj₁ ([s] ⊢Δ [σ])
      [h]' = proj₁ ([h] ⊢Δ [σ])
      [t]' = proj₁ ([t] ⊢Δ [σ])
      [hs] = appTerm [A]' [ℕ] [A▹▹ℕ]' [h]' [s]'
      ⊢hs = escapeTerm [ℕ] [hs]
      hs⇒hs = idRedTerm:*: ⊢hs
      ⊢A = escape [A]'
      ⊢s = escapeTerm [A]' [s]'
      ⊢h = escapeTerm [A▹▹ℕ]' [h]'
      ⊢t = conv (escapeTerm [A▹▹A]' [t]') (subst-▹▹ A σ [A▹▹A]')
      ⊢hd = hdⱼ (coiterⱼ ⊢A ⊢s ⊢h ⊢t)
  in redSubst*EqTermℕ [ ⊢hd , ⊢hs , hd-β ⊢A ⊢s ⊢h ⊢t ⇨ id ⊢hs ] hs⇒hs (reflEqTerm [ℕ] [hs])


tl-βᵛ : ∀ {l A s h t}
        ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([A▹▹ℕ] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ ℕ / [Γ])
        ([A▹▹A] : Γ ⊩ᵛ⟨ l ⟩ A ▹▹ A / [Γ])
        ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ A / [Γ] / [A])
        ([h] : Γ ⊩ᵛ⟨ l ⟩ h ∷ A ▹▹ ℕ / [Γ] / [A▹▹ℕ])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ▹▹ A / [Γ] / [A▹▹A])
        ([coiter-tl] : Γ ⊩ᵛ⟨ l ⟩ coiter A (t ∘ s) h t ∷ Str / [Γ]  / Strᵛ [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ tl (coiter A s h t) ≡ coiter A (t ∘ s) h t ∷ Str / [Γ] / Strᵛ [Γ]
tl-βᵛ {l = l} {A} {s} {h} {t} [Γ] [A] [A▹▹ℕ] [A▹▹A] [s] [h] [t] [coiter-tl] =
  proj₂ (redSubstTermᵛ {A = Str} {t = tl (coiter A s h t)} {u = coiter A (t ∘ s) h t} {l = l} [Γ] [tl-β] (Strᵛ [Γ]) [coiter-tl] )
  where
    [tl-β] : _ ⊩ᵛ tl (coiter A s h t) ⇒ coiter A (t ∘ s) h t ∷ Str / [Γ]
    [tl-β] {σ = σ} ⊢Δ [σ] =
      let [A]' = proj₁ ([A] ⊢Δ [σ])
          [A▹▹ℕ]' = proj₁ ([A▹▹ℕ] ⊢Δ [σ])
          [A▹▹A]' = proj₁ ([A▹▹A] ⊢Δ [σ])
      in tl-β (escape [A]')
              (escapeTerm [A]' (proj₁ ([s] ⊢Δ [σ])))
              (escapeTerm [A▹▹ℕ]' (proj₁ ([h] ⊢Δ [σ])))
              (conv (escapeTerm [A▹▹A]' (proj₁ ([t] ⊢Δ [σ]))) (subst-▹▹ A σ [A▹▹A]'))
