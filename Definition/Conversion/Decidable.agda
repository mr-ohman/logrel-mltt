module Definition.Conversion.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.LogicalRelation.Consequences.Syntactic
open import Definition.LogicalRelation.Consequences.InverseUniv

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE


lemx : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑ A → m PE.≡ n
lemx (var x) = PE.refl

mutual
  dec~ : ∀ {k l R T Γ}
       → Γ ⊢ k ∷ R → Γ ⊢ l ∷ T
       → Neutral l → Neutral k
       → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~ (var x₁ x₂) (var x₃ x₄) (var m) (var n) with m ≟ n
  dec~ {T = T} (var x₁ x₂) (var x₃ x₄) (var n) (var .n) | yes PE.refl =
    yes (T , var (var x₃ x₄))
  dec~ (var x₁ x₂) (var x₃ x₄) (var m) (var n) | no ¬p =
    no (λ { (A , x) → ¬p (lemx x) })

  dec~ k₁ l (var n) (_∘_ neL) = no (λ { (_ , ()) })
  dec~ k₁ l (var n) (natrec neL) = no (λ { (_ , ()) })
  dec~ k₂ l (_∘_ neK) (var n) = no (λ { (_ , ()) })

  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) with dec~ k₁ l neK neL
  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | yes (A , k~l) =
    {!!}
  dec~ (k₁ ∘ k₂) (l ∘ l₁) (_∘_ neK) (_∘_ neL) | no ¬p =
    no (λ { (_ , app k~l x) → ¬p ({!!} , {!!}) })

  dec~ k₂ l (_∘_ neK) (natrec neL) = no (λ { (_ , ()) })
  dec~ k₂ l (natrec neK) (var n) = no (λ { (_ , ()) })
  dec~ k₂ l (natrec neK) (_∘_ neL) = no (λ { (_ , ()) })

  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    with dec~ k₃ l₂ neK neL
  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | yes (A , k~l) = {!!}
  dec~ (natrec x k₁ k₂ k₃) (natrec x₁ l l₁ l₂) (natrec neK) (natrec neL)
    | no ¬p = no (λ { (_ , natrec x₂ x₃ x₄ k~l) → ¬p (ℕ , {!!}) })

  dec~ k (conv l x) neK neL = dec~ k l neK neL
  dec~ (conv k x) l neK neL = dec~ k l neK neL


  decConv : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Dec (Γ ⊢ A [conv↓] B)
  decConv A B = {!!}


  decConvTerm : ∀ {t u A Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConvTerm t u = {!!}


  decConv' : ∀ {t u A B Γ} → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B
           → Dec (Γ ⊢ A [conv↓] B) × Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv' t u with decConv (syntacticTerm t) (syntacticTerm u)
  decConv' t u | yes p = yes p , decConvTerm t (conv u (sym (soundnessConv↓ p)))
  decConv' t u | no ¬p = no ¬p , {!!}
