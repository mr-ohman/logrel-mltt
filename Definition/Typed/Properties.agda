module Definition.Typed.Properties where

open import Data.Product

open import Tools.Context
open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties using (wkIndex-step; wkIndex-lift; wk-β; wk-β-natrec)
open import Definition.Typed
open import Data.Nat renaming (ℕ to Nat)
import Relation.Binary.PropositionalEquality as PE


-- Wellformed context extraction

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕ x) = x
wfTerm (Π x ▹ x₁) = wfTerm x
wfTerm (var x x₁) = x
wfTerm (lam x x₁) with wfTerm x₁
wfTerm (lam x₁ x₂) | q ∙ x = q
wfTerm (x ∘ x₁) = wfTerm x₁
wfTerm (zero x) = x
wfTerm (suc x) = wfTerm x
wfTerm (natrec x x₁ x₂ x₃) = wfTerm x₁
wfTerm (conv x x₁) = wfTerm x

wf : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wf (ℕ x) = x
wf (U x) = x
wf (Π x ▹ x₁) = wf x
wf (univ x) = wfTerm x

wfEqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl x) = wfTerm x
wfEqTerm (sym x) = wfEqTerm x
wfEqTerm (trans x x₁) = wfEqTerm x
wfEqTerm (conv x x₁) = wfEqTerm x
wfEqTerm (Π-cong x x₁ x₂) = wfEqTerm x₁
wfEqTerm (app-cong x x₁) = wfEqTerm x
wfEqTerm (β-red x x₁ x₂) = wfTerm x₂
wfEqTerm (fun-ext x x₁ x₂ x₃) = wfTerm x₁
wfEqTerm (suc-cong x) = wfEqTerm x
wfEqTerm (natrec-cong x x₁ x₂ x₃) = wfEqTerm x₂
wfEqTerm (natrec-zero x x₁ x₂) = wfTerm x₁
wfEqTerm (natrec-suc x x₁ x₂ x₃) = wfTerm x

wfEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ x) = wfEqTerm x
wfEq (refl x) = wf x
wfEq (sym x) = wfEq x
wfEq (trans x x₁) = wfEq x
wfEq (Π-cong x x₁ x₂) = wfEq x₁

-- -- Conversion to type/term arrows

-- eqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
-- eqTerm (refl x) = x , x
-- eqTerm (sym t₂) = swap (eqTerm t₂)
-- eqTerm (trans t₁ t₂) = let a , b = eqTerm t₁
--                            c , d = eqTerm t₂
--                        in a , d
-- eqTerm (conv t₁ x) = let a , b = eqTerm t₁
--                      in  conv a x , conv b x
-- eqTerm (Π-cong t t₁) = let a , b = eqTerm t
--                            c , d = eqTerm t₁
--                        in  Π a ▹ c , Π b ▹ {!d!}
-- eqTerm (app-cong t t₁) = let a , b = eqTerm t
--                              c , d = eqTerm t₁
--                          in  a ∘ c , {!b!} ∘ d
-- eqTerm (β-red x x₁) = lam x ∘ x₁ , {!!}
-- eqTerm (fun-ext x x₁ t) = x , x₁
-- eqTerm (natrec-cong x t t₁) = let a , b = eqTerm t
--                                   c , d = eqTerm t₁
--                               in  (natrec {!!} a c) , {!!}
-- eqTerm (natrec-zero x x₁ x₂) = natrec x x₁ x₂ ∘ zero (wfTerm x₁) , x₁
-- eqTerm (natrec-suc x x₁ x₂ x₃) = natrec x₁ x₂ x₃ ∘ suc x
--                                , ({!x₃!} ∘ x) ∘ (natrec x₁ x₂ x₃ ∘ x)
-- eqTerm (suc-cong t) = let a , b = eqTerm t
--                       in  suc a , suc b

-- eq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
-- eq (univ x) = let a , b = eqTerm x
--               in univ a , univ b
-- eq (refl x) = x , x
-- eq (sym e) = swap (eq e)
-- eq (trans e e₁) = let a , b = eq e
--                       c , d = eq e₁
--                   in  a , d
-- eq (Π-cong e e₁) = let a , b = eq e
--                        c , d = eq e₁
--                    in  Π a ▹ c , Π b ▹ {!d!}

-- substEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A → Γ ⊢ B
-- substEq e _ = proj₂ (eq e)

-- -- Term to type arrow

-- typeOfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ A
-- typeOfTerm (var x₁ x₂) = {!!}
-- typeOfTerm (ℕ x) = U x
-- typeOfTerm (Π t ▹ t₁) = U (wfTerm t)
-- typeOfTerm (lam t₁) with wfTerm t₁
-- typeOfTerm (lam t₁) | x ∙ x₁ = Π x₁ ▹ typeOfTerm t₁
-- typeOfTerm (t ∘ t₁) = {!!}
-- typeOfTerm (zero x) = ℕ x
-- typeOfTerm (suc t) = typeOfTerm t
-- typeOfTerm (natrec x t t₁) = Π ℕ (wfTerm t) ▹ x
-- typeOfTerm (conv t₁ x) = substEq x (typeOfTerm t₁)

-- Weakening
-- The definition of _⊆_ in Tools.Context is not correct for dependent types
-- There's a new correct one in Untyped.
-- The remaining goals here in wkIndex are provable.
-- It's commond to define
-- _•_                :  Wk → Wk → Wk
-- id      • η′       =  η′
-- step η  • η′       =  step  (η • η′)
-- lift η  • id       =  lift  η
-- lift η  • step η′  =  step  (η • η′)
-- lift η  • lift η′  =  lift  (η • η′)
-- then prove composition commutes with wk
-- U.wk p (U.wk q t) ≡ W.wk (p ∙ q) t
-- and then prove things like
-- step id ∙ p ≡ lift p ∙ step id
wkIndex : ∀ {Γ Δ x A} → (pr : Γ ⊆ Δ) →
        let Δ' = Δ
            A' = U.wk (toWk pr) A
            x' = wkNat (toWk pr) x
        in  ⊢ Δ' → x ∷ A ∈ Γ → x' ∷ A' ∈ Δ'
wkIndex base ⊢Δ ()
wkIndex (step pr) (⊢Δ ∙ x) i = let r = (wkIndex pr ⊢Δ i) in PE.subst (\ x → _ ∷ x ∈ _) (wkIndex-step (toWk pr)) (there r)
wkIndex (lift pr) (⊢Δ ∙ x) (there i) = PE.subst (\ x → _ ∷ x ∈ _) (wkIndex-lift (toWk pr)) (there (wkIndex pr ⊢Δ i))
wkIndex (lift pr) ⊢Δ here = PE.subst (let G = _; n = _ in \ x → n ∷ x ∈ G) (wkIndex-lift (toWk pr)) here

mutual
  wk : ∀ {Γ Δ A} → (pr : Γ ⊆ Δ) →
     let Δ' = Δ
         A' = U.wk (toWk pr) A
     in  ⊢ Δ' → Γ ⊢ A → Δ' ⊢ A'
  wk pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wk pr ⊢Δ (U x) = U ⊢Δ
  wk pr ⊢Δ (Π A ▹ A₁) = let x = wk pr ⊢Δ A
                        in  Π x ▹ (wk (lift pr) (⊢Δ ∙ x) A₁)
  wk pr ⊢Δ (univ x) = univ (wkTerm pr ⊢Δ x)

  wkTerm : ∀ {Γ Δ A t} → (pr : Γ ⊆ Δ) →
         let Δ' = Δ
             A' = U.wk (toWk pr) A
             t' = U.wk (toWk pr) t
         in ⊢ Δ' → Γ ⊢ t ∷ A → Δ' ⊢ t' ∷ A'
  wkTerm pr ⊢Δ (ℕ x) = ℕ ⊢Δ
  wkTerm pr ⊢Δ (Π t ▹ t₁) = let x = wkTerm pr ⊢Δ t
                            in  Π x ▹ (wkTerm (lift pr) (⊢Δ ∙ univ x) t₁)
  wkTerm pr ⊢Δ (var x₁ x₂) = var ⊢Δ (wkIndex pr ⊢Δ x₂)
  wkTerm pr ⊢Δ (lam t t₁) = let x = wk pr ⊢Δ t
                            in lam x (wkTerm (lift pr) (⊢Δ ∙ x) t₁)
  wkTerm pr ⊢Δ (_∘_ {G = G} t t₁) = PE.subst (λ x → _ ⊢ _ ∷ x)
                                             (PE.sym (wk-β G))
                                             (wkTerm pr ⊢Δ t ∘ wkTerm pr ⊢Δ t₁)
  wkTerm pr ⊢Δ (zero x) = zero ⊢Δ
  wkTerm pr ⊢Δ (suc t) = suc (wkTerm pr ⊢Δ t)
  wkTerm {Δ = Δ} pr ⊢Δ (natrec {G = G} {s = s} x t t₁ t₂) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (natrec (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                     (PE.subst (λ x₁ → _ ⊢ _ ∷ x₁) (wk-β G) (wkTerm pr ⊢Δ t))
                     (PE.subst (λ x₁ → Δ ⊢ U.wk (toWk pr) s ∷ x₁) (wk-β-natrec (toWk pr) G) (wkTerm pr ⊢Δ t₁))
                     (wkTerm pr ⊢Δ t₂))
  wkTerm pr ⊢Δ (conv t₁ x) = conv (wkTerm pr ⊢Δ t₁) (wkEq pr ⊢Δ x)

  wkEq : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
       let Δ' = Δ
           A' = U.wk (toWk pr) A
           B' = U.wk (toWk pr) B
       in ⊢ Δ' → Γ ⊢ A ≡ B → Δ' ⊢ A' ≡ B'
  wkEq pr ⊢Δ (univ x) = univ (wkEqTerm pr ⊢Δ x)
  wkEq pr ⊢Δ (refl x) = refl (wk pr ⊢Δ x)
  wkEq pr ⊢Δ (sym x) = sym (wkEq pr ⊢Δ x)
  wkEq pr ⊢Δ (trans x x₁) = trans (wkEq pr ⊢Δ x) (wkEq pr ⊢Δ x₁)
  wkEq pr ⊢Δ (Π-cong x x₁ x₂) = let y = wk pr ⊢Δ x
                                in  Π-cong y (wkEq pr ⊢Δ x₁) (wkEq (lift pr) (⊢Δ ∙ y) x₂)

  wkEqTerm : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let Δ' = Δ
               A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ' → Γ ⊢ t ≡ u ∷ A → Δ' ⊢ t' ≡ u' ∷ A'
  wkEqTerm pr ⊢Δ (refl x) = refl (wkTerm pr ⊢Δ x)
  wkEqTerm pr ⊢Δ (sym x) = sym (wkEqTerm pr ⊢Δ x)
  wkEqTerm pr ⊢Δ (trans x x₁) = trans (wkEqTerm pr ⊢Δ x) (wkEqTerm pr ⊢Δ x₁)
  wkEqTerm pr ⊢Δ (conv x x₁) = conv (wkEqTerm pr ⊢Δ x) (wkEq pr ⊢Δ x₁)
  wkEqTerm pr ⊢Δ (Π-cong x x₁ x₂) = let y = wk pr ⊢Δ x
                                    in  Π-cong y (wkEqTerm pr ⊢Δ x₁)
                                                 (wkEqTerm (lift pr) (⊢Δ ∙ y) x₂)
  wkEqTerm pr ⊢Δ (app-cong {G = G} x x₁) =
    PE.subst (λ x₂ → _ ⊢ _ ≡ _ ∷ x₂)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm pr ⊢Δ x) (wkEqTerm pr ⊢Δ x₁))
  wkEqTerm pr ⊢Δ (β-red {a = a} {b = b} {G = G} x x₁ x₂) =
    let y = wk pr ⊢Δ x
    in  PE.subst (λ x₂ → _ ⊢ _ ≡ _ ∷ x₂)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x₂ → _ ⊢ U.wk (toWk pr) ((lam b) ∘ a) ≡ x₂ ∷ _)
                           (PE.sym (wk-β b))
                           (β-red y (wkTerm (lift pr) (⊢Δ ∙ y) x₁) (wkTerm pr ⊢Δ x₂)))
  wkEqTerm pr ⊢Δ (fun-ext x x₁ x₂ x₃) =
    let y = wk pr ⊢Δ x
    in fun-ext y (wkTerm pr ⊢Δ x₁)
                 (wkTerm pr ⊢Δ x₂)
                 (PE.subst (λ t → _ ⊢ t ∘ _ ≡ _ ∷ _)
                           (PE.sym (wkIndex-lift (toWk pr)))
                           (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ∷ _)
                                     (PE.sym (wkIndex-lift (toWk pr)))
                                     (wkEqTerm (lift pr) (⊢Δ ∙ y) x₃)))
  wkEqTerm pr ⊢Δ (suc-cong x) = suc-cong (wkEqTerm pr ⊢Δ x)
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-cong {s = s} {s' = s'} {F = F} x x₁ x₂ x₃) =
    PE.subst (λ x₄ → Δ ⊢ natrec _ _ _ _ ≡ _ ∷ x₄) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
             (PE.subst (λ x₄ → Δ ⊢ _ ≡ _ ∷ x₄) (wk-β F) (wkEqTerm pr ⊢Δ x₁))
             (PE.subst (λ x₄ → Δ ⊢ U.wk (toWk pr) s ≡ U.wk (toWk pr) s' ∷ x₄) (wk-β-natrec (toWk pr) F) (wkEqTerm pr ⊢Δ x₂))
             (wkEqTerm pr ⊢Δ x₃))
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-zero {z} {s} {F} x x₁ x₂) =
    PE.subst (λ y → Δ ⊢ natrec (U.wk (lift (toWk pr)) F) _ _ _ ≡ _ ∷ y) (PE.sym (wk-β F))
             (natrec-zero (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                          (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) z ∷ y) (wk-β F) (wkTerm pr ⊢Δ x₁))
                          (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) s ∷ y) (wk-β-natrec (toWk pr) F) (wkTerm pr ⊢Δ x₂)))
  wkEqTerm {Δ = Δ} pr ⊢Δ (natrec-suc {n} {z} {s} {F} x x₁ x₂ x₃) =
    PE.subst (λ y → Δ ⊢ natrec (U.wk (lift (toWk pr)) F) _ _ _ ≡ _ ∘ (natrec _ _ _ _) ∷ y) (PE.sym (wk-β F))
             (natrec-suc (wkTerm pr ⊢Δ x)
                         (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x₁)
                         (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) z ∷ y) (wk-β F) (wkTerm pr ⊢Δ x₂))
                         (PE.subst (λ y → Δ ⊢ U.wk (toWk pr) s ∷ y) (wk-β-natrec (toWk pr) F) (wkTerm pr ⊢Δ x₃)))

mutual
  wkRed : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               B' = U.wk (toWk pr) B
           in ⊢ Δ → Γ ⊢ A ⇒ B → Δ ⊢ A' ⇒ B'
  wkRed pr ⊢Δ (univ x) = univ (wkRedTerm pr ⊢Δ x)

  wkRedTerm : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ t' ⇒ u' ∷ A'
  wkRedTerm pr ⊢Δ (conv r x) = conv (wkRedTerm pr ⊢Δ r) (wkEq pr ⊢Δ x)
  wkRedTerm pr ⊢Δ (app-subst {B = B} r x) =
    PE.subst (λ x₁ → _ ⊢ _ ⇒ _ ∷ x₁) (PE.sym (wk-β B))
             (app-subst (wkRedTerm pr ⊢Δ r) (wkTerm pr ⊢Δ x))
  wkRedTerm pr ⊢Δ (β-red {A} {B} {a} {t} x x₁ x₂) =
    PE.subst (λ x₃ → _ ⊢ _ ⇒ _ ∷ x₃) (PE.sym (wk-β B))
             ((PE.subst (λ x₂ → _ ⊢ U.wk (toWk pr) ((lam t) ∘ a) ⇒ x₂ ∷ _) (PE.sym (wk-β t))
                        (let y = wk pr ⊢Δ x
                         in  β-red y (wkTerm (lift pr) (⊢Δ ∙ y) x₁) (wkTerm pr ⊢Δ x₂))))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-subst {C} {g = g} x x₁ x₂ r) =
    PE.subst (λ x₃ → _ ⊢ natrec _ _ _ _ ⇒ _ ∷ x₃) (PE.sym (wk-β C))
             (natrec-subst (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                           (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                     (wkTerm pr ⊢Δ x₁))
                           (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃)
                                     (wk-β-natrec (toWk pr) C)
                                     (wkTerm pr ⊢Δ x₂))
                           (wkRedTerm pr ⊢Δ r))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-zero {C} {g = g} x x₁ x₂) =
    PE.subst (λ x₃ → _ ⊢ natrec (U.wk (lift (toWk pr)) C) _ _ _ ⇒ _ ∷ x₃) (PE.sym (wk-β C))
             (natrec-zero (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x)
                          (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                    (wkTerm pr ⊢Δ x₁))
                          (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃) (wk-β-natrec (toWk pr) C)
                                    (wkTerm pr ⊢Δ x₂)))
  wkRedTerm {Δ = Δ} pr ⊢Δ (natrec-suc {C} {g = g} x x₁ x₂ x₃) =
    PE.subst (λ x₄ → _ ⊢ natrec _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ ∷ x₄) (PE.sym (wk-β C))
             (natrec-suc (wkTerm pr ⊢Δ x)
                         (wk (lift pr) (⊢Δ ∙ ℕ ⊢Δ) x₁)
                         (PE.subst (λ x₃ → _ ⊢ _ ∷ x₃) (wk-β C)
                                   (wkTerm pr ⊢Δ x₂))
                         (PE.subst (λ x₃ → Δ ⊢ U.wk (toWk pr) g ∷ x₃) (wk-β-natrec (toWk pr) C)
                                   (wkTerm pr ⊢Δ x₃)))

wkRed* : ∀ {Γ Δ A B} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               B' = U.wk (toWk pr) B
           in ⊢ Δ → Γ ⊢ A ⇒* B → Δ ⊢ A' ⇒* B'
wkRed* pr ⊢Δ (id A) = id (wk pr ⊢Δ A)
wkRed* pr ⊢Δ (x ⇨ r) = (wkRed pr ⊢Δ x) ⇨ (wkRed* pr ⊢Δ r)

wkRed*Term : ∀ {Γ Δ A t u} → (pr : Γ ⊆ Δ) →
           let A' = U.wk (toWk pr) A
               t' = U.wk (toWk pr) t
               u' = U.wk (toWk pr) u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ t' ⇒* u' ∷ A'
wkRed*Term pr ⊢Δ (id t) = id (wkTerm pr ⊢Δ t)
wkRed*Term pr ⊢Δ (x ⇨ r) = (wkRedTerm pr ⊢Δ x) ⇨ (wkRed*Term pr ⊢Δ r)

-- -- Inverse typing lemmas

-- inversion-zero : ∀ {Γ C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
-- inversion-zero (zero x) = refl (ℕ x)
-- inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

-- inversion-suc : ∀ {Γ t C} → Γ ⊢ suc t ∷ C → Γ ⊢ C ≡ ℕ
-- inversion-suc (suc x) = refl (ℕ (wfTerm x))
-- inversion-suc (conv x x₁) = trans (sym x₁) (inversion-suc x)

-- inversion-natrec : ∀ {Γ c g A C} → Γ ⊢ natrec C c g ∷ A → Γ ⊢ A ≡ Π ℕ ▹ C
-- inversion-natrec (natrec x d d₁) = Π-cong (refl (ℕ (wfTerm d))) (refl x)
-- inversion-natrec (conv d x) = trans (sym x) (inversion-natrec d)

-- inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ a) ∷ A →
--   ∃₂ λ F G → Γ ⊢ f ∷ Π F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
-- inversion-app (d ∘ d₁) = _ , _ , d , d₁ , refl (typeOfTerm (d ∘ d₁))
-- inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
--                            in  a , b , c , d , trans (sym x) e

-- -- Π-injectivity needed to prove this?
-- inversion-app-natrec : ∀ {Γ c g m A C} → Γ ⊢ natrec C c g ∘ m ∷ A
--                      → Γ ⊢ A ≡ C [ m ]
-- inversion-app-natrec (x ∘ x₁) = {!!}
-- inversion-app-natrec (conv x x₁) = trans (sym x₁) (inversion-app-natrec x)

-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst x x₁ x₂ x₃) = natrec-cong (refl x) (refl x₁) (refl x₂) (subsetTerm x₃)
subsetTerm (natrec-zero x x₁ x₂) = natrec-zero x x₁ x₂
subsetTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc x x₁ x₂ x₃
subsetTerm (app-subst x x₁) = app-cong (subsetTerm x) (refl x₁)
subsetTerm (β-red x x₁ x₂) = β-red x x₁ x₂
subsetTerm (conv x x₁) = conv (subsetTerm x) x₁

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ x) = univ (subsetTerm x)

subset*Term : ∀ {Γ A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (x ⇨ x₁) = trans (subsetTerm x) (subset*Term x₁)

subset* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (x ⇨ x₁) = trans (subset x) (subset* x₁)

-- mutual
--   substEqTerm : ∀ {Γ t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A
--   substEqTerm (refl x) A = A
--   substEqTerm (sym x) A = {!!}
--   substEqTerm (trans x x₁) A = substEqTerm x₁ (substEqTerm x A)
--   substEqTerm (conv x x₁) A₁ = {!!}
--   substEqTerm (Π-cong x x₁ x₂) A = {!!}
--   substEqTerm (app-cong x x₁) A = {!!}
--   substEqTerm (β-red x x₁ x₂) A = {!!}
--   substEqTerm (fun-ext x x₁ x₂ x₃) A = {!!}
--   substEqTerm (suc-cong x) A = suc {!!}
--   substEqTerm (natrec-cong x x₁ x₂ x₃) A = {!!}
--   substEqTerm (natrec-zero x x₁ x₂) A = {!!}
--   substEqTerm (natrec-suc x x₁ x₂ x₃) A = {!!}

--   substEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A → Γ ⊢ B
--   substEq (univ x) A = {!!}
--   substEq (refl x) A = A
--   substEq (sym eq) A = {!!}
--   substEq (trans eq eq₁) A = substEq eq₁ (substEq eq A)
--   substEq (Π-cong x eq eq₁) A = {!!}
