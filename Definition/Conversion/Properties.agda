module Definition.Conversion.Properties where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.LogicalRelation.Consequences.Syntactic

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

mutual
  ~-subset : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  ~-subset (var x x₁) = refl (var x x₁)
  ~-subset (app k~l x x₁) = app-cong (~-subset k~l) (convSubsetTerm x₁)
  ~-subset (suc k~l x) = suc-cong (~-subset k~l)
  ~-subset (natrec k~l x x₁ x₂ x₃) =
    natrec-cong (convSubset x₁) (convSubsetTerm x₃)
                (convSubsetTerm x₂) (~-subset k~l)

  convSubset : ∀ {A B Γ} → Γ ⊢ A [conv] B → Γ ⊢ A ≡ B
  convSubset (reduction x x₁ c) =
    trans (subset* x) (trans (convSubset c) (sym (subset* x₁)))
  convSubset (U-refl ⊢Γ) = refl (U ⊢Γ)
  convSubset (ℕ-refl ⊢Γ) = refl (ℕ ⊢Γ)
  convSubset (ne x x₁ x₂ x₃) = univ (~-subset x)
  convSubset (Π-cong c c₁) =
    let x = convSubset c
        F = proj₁ (syntacticEq x)
    in  Π-cong F x (convSubset c₁)

  convSubsetTerm : ∀ {a b A Γ} → Γ ⊢ a [conv] b ∷ A → Γ ⊢ a ≡ b ∷ A
  convSubsetTerm (reduction x x₁ x₂ c) =
    let c'  = convSubsetTerm c
        x₂' = subset*Term x₂
        x₁' = subset*Term x₁
        x'  = subset* x
    in  conv (trans x₁' (trans c' (sym x₂'))) (sym x')
  convSubsetTerm (ℕ-ins x x₁ x₂) = ~-subset x
  convSubsetTerm (ne-ins x x₁ x₂ x₃) = ~-subset x
  convSubsetTerm (univ x x₁ x₂) = {!!}
  convSubsetTerm (zero-refl ⊢Γ) = refl (zero ⊢Γ)
  convSubsetTerm (suc-cong c) = suc-cong (convSubsetTerm c)
  convSubsetTerm (fun-ext x x₁ c) =
    let q = proj₁ (syntacticΠ (syntacticTerm x))
    in  fun-ext q x x₁ (convSubsetTerm c)


lemx : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑ A → m PE.≡ n
lemx (var x x₁) = PE.refl

lemy : ∀ {n R T Γ} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
lemy here here = PE.refl
lemy (there n∷R) (there n∷T) with lemy n∷R n∷T
lemy (there n∷R) (there n∷T) | PE.refl = PE.refl

mutual
  dec~ : ∀ {k l R T Γ}
       → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
       → Neutral l → Neutral k
       → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~ (var x₁ x₂) (var x₃ x₄) (var m) (var n) with m ≟ n
  dec~ {T = T} (var x₁ x₂) (var x₃ x₄) (var n) (var .n) | yes PE.refl =
    yes (T , var x₁ x₄)
  dec~ (var x₁ x₂) (var x₃ x₄) (var m) (var n) | no ¬p =
    no (λ { (A , x) → ¬p (lemx x) })
  dec~ k (conv l x₃) (var m) (var x) = dec~ k l (var m) (var x)
  dec~ (conv k x) l (var m) (var n) = dec~ k l (var m) (var n)

  dec~ k₁ l (var n) (_∘_ neL) = no (λ { (_ , ()) })
  dec~ k₁ l (var n) (natrec neL) = no (λ { (_ , ()) })
  dec~ k₂ l (_∘_ neK) (var n) = no (λ { (_ , ()) })

  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) with dec~ k₁ l neK neL
  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l) =
    {!!}
  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | no ¬p =
    no (λ { (_ , app k~l x x₁) → ¬p (_ , k~l) })
  dec~ k (conv l x) (_∘_ neK) (_∘_ neL) = dec~ k l (_∘_ neK) (_∘_ neL)
  dec~ (conv k x) l (_∘_ neK) (_∘_ neL) = dec~ k l (_∘_ neK) (_∘_ neL)

  dec~ k₂ l (_∘_ neK) (natrec neL) = no (λ { (_ , ()) })
  dec~ k₂ l (natrec neK) (var n) = no (λ { (_ , ()) })
  dec~ k₂ l (natrec neK) (_∘_ neL) = no (λ { (_ , ()) })

  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    with dec~ k₃ l₂ neK neL
  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) = {!!}
  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | no ¬p = no (λ { (_ , natrec k~l x₂ x₃ x₄ x₅) → ¬p (ℕ , k~l) })
  dec~ k (conv l x₁) (natrec neK) (natrec neL) = dec~ k l (natrec neK) (natrec neL)
  dec~ (conv k x) l (natrec neK) (natrec neL) = dec~ k l (natrec neK) (natrec neL)


  decConv : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A [conv] B)
  decConv A B = {!!}


  decConvTerm : ∀ {t u A Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t [conv] u ∷ A)
  decConvTerm t u = {!!}


  decConv' : ∀ {t u A B Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B
           → Dec (Γ ⊢ A [conv] B) × Dec (Γ ⊢ t [conv] u ∷ A)
  decConv' t u with decConv (syntacticTerm t) (syntacticTerm u)
  decConv' t u | yes p = yes p , decConvTerm t (conv u (sym (convSubset p)))
  decConv' t u | no ¬p = no ¬p , {!!}
