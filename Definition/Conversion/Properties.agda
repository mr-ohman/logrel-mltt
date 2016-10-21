module Definition.Conversion.Properties where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PE

mutual
  ~-subset : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑ A → Γ ⊢ k ≡ l ∷ A
  ~-subset (var x₁) = refl (var {!!} x₁)
  ~-subset (app k~l x x₁) = app-cong (~-subset k~l) (convSubsetTerm {!!} x₁)
  ~-subset (suc k~l x) = suc-cong (~-subset k~l)
  ~-subset (natrec k~l x x₁ x₂ x₃) = natrec-cong {!!} {!!} {!!} (~-subset k~l)

  convSubsetTerm : ∀ {a b A Γ} → ⊢ Γ → Γ ⊢ a [conv] b ∷ A → Γ ⊢ a ≡ b ∷ A
  convSubsetTerm ⊢Γ (tmp x x₁ x₂ c) = let c'  = convSubsetTerm ⊢Γ c
                                          x₂' = subset*Term x₂
                                          x₁' = subset*Term x₁
                                          x'  = subset* x
                                      in  conv (trans x₁' (trans c' (sym x₂'))) (sym x')
  convSubsetTerm ⊢Γ (ℕ-ins x x₁ x₂) = {!!}
  convSubsetTerm ⊢Γ (ne-ins x x₁ x₂ x₃) = {!!}
  convSubsetTerm ⊢Γ (tmp2 x x₁ x₂) = {!!}
  convSubsetTerm ⊢Γ zero-refl = refl (zero ⊢Γ)
  convSubsetTerm ⊢Γ (suc-cong c) = {!!}
  convSubsetTerm ⊢Γ (fun-ext x x₁ c) = {!!}

convSubset : ∀ {A B Γ} → ⊢ Γ → Γ ⊢ A [conv] B → Γ ⊢ A ≡ B
convSubset = {!!}

lemx : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑ A → m PE.≡ n
lemx (var x₁) = PE.refl

lemy : ∀ {n R T Γ} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
lemy here here = PE.refl
lemy (there n∷R) (there n∷T) with lemy n∷R n∷T
lemy (there n∷R) (there n∷T) | PE.refl = PE.refl

lemz : ∀ {k u n Γ} → ∃ (_⊢_~_↑_ Γ (k ∘ u) (var n)) → ⊥
lemz (proj₁ , ())

dec~ : ∀ {k l R T Γ}
     → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
     → Neutral l → Neutral k
     → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
dec~ (var x₁ x₂) (var x₃ x₄) (var m) (var n) with m ≟ n
dec~ {T = T} (var x₁ x₂) (var x₃ x₄) (var n) (var .n) | yes PE.refl =
  yes (T , var x₄)
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
