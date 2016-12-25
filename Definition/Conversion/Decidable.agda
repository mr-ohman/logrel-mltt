{-# OPTIONS --without-K #-}

module Definition.Conversion.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.InverseUniv
open import Definition.LogicalRelation.Consequences.Reduction

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE


lemx : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑ A → n PE.≡ m
lemx (var x) = PE.refl

decNeutral : (t : Term) → Dec (Neutral t)
decNeutral U = no (λ ())
decNeutral (Π t ▹ t₁) = no (λ ())
decNeutral ℕ = no (λ ())
decNeutral (var x) = yes (var x)
decNeutral (lam t) = no (λ ())
decNeutral (t ∘ t₁) with decNeutral t
decNeutral (t ∘ t₁) | yes p = yes (_∘_ p)
decNeutral (t ∘ t₁) | no ¬p = no (λ { (_∘_ x) → ¬p x })
decNeutral zero = no (λ ())
decNeutral (suc t) = no (λ ())
decNeutral (natrec t t₁ t₂ t₃) with decNeutral t₃
decNeutral (natrec t t₁ t₂ t₃) | yes p = yes (natrec p)
decNeutral (natrec t t₁ t₂ t₃) | no ¬p = no (λ { (natrec x) → ¬p x })

decWhnf : (t : Term) → Dec (Whnf t)
decWhnf U = yes U
decWhnf (Π t ▹ t₁) = yes Π
decWhnf ℕ = yes ℕ
decWhnf (var x) = yes (ne (var x))
decWhnf (lam t) = yes lam
decWhnf (t ∘ t₁) with decNeutral (t ∘ t₁)
decWhnf (t ∘ t₁) | yes p = yes (ne p)
decWhnf (t ∘ t₁) | no ¬p = no (λ { (ne x) → ¬p x })
decWhnf zero = yes zero
decWhnf (suc t) = yes suc
decWhnf (natrec t t₁ t₂ t₃) with decNeutral (natrec t t₁ t₂ t₃)
decWhnf (natrec t t₁ t₂ t₃) | yes p = yes (ne p)
decWhnf (natrec t t₁ t₂ t₃) | no ¬p = no (λ { (ne x) → ¬p x })

mutual
  dec~↑ : ∀ {k l R T Γ}
        → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
        → Neutral k → Neutral l
        → Dec (∃ λ A → Γ ⊢ A × (Γ ⊢ k ~ l ↑ A))
  dec~↑ (var x₁ x₂) (var x₃ x₄) (var m) (var n) with m ≟ n
  dec~↑ {T = T} (var x₁ x₂) (var x₃ x₄) (var n) (var .n) | yes PE.refl =
    yes (T , syntacticTerm (var x₃ x₄) , var (var x₃ x₄))
  dec~↑ (var x₁ x₂) (var x₃ x₄) (var m) (var n) | no ¬p =
    no (λ { (A , x) → ¬p {!!} })

  dec~↑ k₁ l (var n) (_∘_ neL) = no (λ { (_ , _ , ()) })
  dec~↑ k₁ l (var n) (natrec neL) = no (λ { (_ , _ , ()) })
  dec~↑ k₂ l (_∘_ neK) (var n) = no (λ { (_ , _ , ()) })

  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) with dec~↓ k₁ l neK neL
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l) =
    {!!}
  dec~↑ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | no ¬p =
    no (λ { (_ , _ , app k~l x) → ¬p (_ , k~l) })

  dec~↑ k₂ l (_∘_ neK) (natrec neL) = no (λ { (_ , _ , ()) })
  dec~↑ k₂ l (natrec neK) (var n) = no (λ { (_ , _ , ()) })
  dec~↑ k₂ l (natrec neK) (_∘_ neL) = no (λ { (_ , _ , ()) })

  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    with dec~↓ k₃ l₂ neK neL
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) = {!!}
  dec~↑ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | no ¬p = no (λ { (_ , _ , natrec x₂ x₃ x₄ k~l) → ¬p (ℕ , k~l) })

  dec~↑ k (conv l x) neK neL = dec~↑ k l neK neL
  dec~↑ (conv k x) l neK neL = dec~↑ k l neK neL

  dec~↓ : ∀ {k l R T Γ}
        → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
        → Neutral k → Neutral l
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ k l neK neL with dec~↑ k l neK neL
  dec~↓ k₁ l₁ neK neL | yes (A , ⊢A , k~l) =
    let B , whnfB , D = fullyReducible ⊢A
    in  yes (B , [~] A (red D) whnfB k~l)
  dec~↓ k₁ l₁ neK neL | no ¬p =
    no (λ { (A , [~] B D whnfA k~l) → ¬p (B , proj₁ (syntacticRed D) , k~l) })


  decConv↑ : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ A B with fullyReducible A | fullyReducible B
  decConv↑ A B | A' , whnfA' , [ _ , ⊢A' , D ] | B' , whnfB' , [ _ , ⊢B' , D' ]
           with decConv↓ ⊢A' ⊢B'
                         whnfA' whnfB'
  decConv↑ A B | A' , whnfA' , [ _ , ⊢A' , D ] | B' , whnfB' , [ _ , ⊢B' , D' ]
               | yes p = yes ([↑] A' B' D D' whnfA' whnfB' p)
  decConv↑ A B | A' , whnfA' , [ _ , ⊢A' , D ] | B' , whnfB' , [ _ , ⊢B' , D' ]
               | no ¬p =
    no (λ { ([↑] A₁ B₁ D₁ D₁' whnfA₁ whnfB₁ A₁<>B₁)
        → ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y)
                        (whrDet*' (D₁ , whnfA₁) (D , whnfA'))
                        (whrDet*' (D₁' , whnfB₁) (D' , whnfB'))
                        A₁<>B₁) })

  decConv↓ : ∀ {A B Γ}
           → Γ ⊢ A → Γ ⊢ B
           → Whnf A → Whnf B
           → Dec (Γ ⊢ A [conv↓] B)
  decConv↓ A B whnfA whnfB = {!!}


  decConv↑Term : ∀ {t u A Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term t u with fullyReducibleTerm t | fullyReducibleTerm u
                      | fullyReducible (syntacticTerm t)
  decConv↑Term t u | t' , whnfT' , [ _ , ⊢t' , d ]
                   | u' , whnfU' , [ _ , ⊢u' , d' ]
                   | A' , whnfA' , [ _ , ⊢A' , D ]
                   with decConv↓Term (conv ⊢t' (subset* D))
                                     (conv ⊢u' (subset* D))
                                     whnfT' whnfU' whnfA'
  decConv↑Term t u | t' , whnfT' , [ _ , ⊢t' , d ]
                   | u' , whnfU' , [ _ , ⊢u' , d' ]
                   | A' , whnfA' , [ _ , ⊢A' , D ] | yes p =
    yes ([↑]ₜ A' t' u' D (conv* d (subset* D)) (conv* d' (subset* D))
              whnfA' whnfT' whnfU' p)
  decConv↑Term t u | t' , whnfT' , [ _ , ⊢t' , d ]
                   | u' , whnfU' , [ _ , ⊢u' , d' ]
                   | A' , whnfA' , [ _ , ⊢A' , D ] | no ¬p =
    no (λ { ([↑]ₜ A₁ t₁ u₁ D₁ d₁ d₁' whnfA₁ whnfT₁ whnfU₁ t₁<>u₁)
        → ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z)
                        (whrDet* (d₁ , whnfT₁) (conv* d (subset* D₁) , whnfT'))
                        (whrDet* (d₁' , whnfU₁) (conv* d' (subset* D₁) , whnfU'))
                        (whrDet*' (D₁ , whnfA₁) (D , whnfA'))
                        t₁<>u₁) })

  decConv↓Term : ∀ {t u A Γ}
               → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A
               → Whnf t → Whnf u → Whnf A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv↓Term t u = {!!}


  -- decConv' : ∀ {t u A B Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B
  --          → Dec (Γ ⊢ A [conv↓] B) × Dec (Γ ⊢ t [conv↓] u ∷ A)
  -- decConv' t u with decConv↓ (syntacticTerm t) (syntacticTerm u)
  -- decConv' t u | yes p = yes p , decConv↓Term t (conv u (sym (soundnessConv↓ p)))
  -- decConv' t u | no ¬p = no ¬p , {!!}
