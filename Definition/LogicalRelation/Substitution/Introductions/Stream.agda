{-# OPTIONS --without-K --safe --guardedness #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Stream {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Nat
-- open import Definition.LogicalRelation.MaybeEmbed
open import Definition.LogicalRelation.Irrelevance

open import Tools.Nat
open import Tools.Product

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

