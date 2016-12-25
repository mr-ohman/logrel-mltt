{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE


fullyReducible' : ∀ {A Γ l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
fullyReducible' (U' .⁰ 0<1 ⊢Γ) = U , U , idRed:*: (U ⊢Γ)
fullyReducible' (ℕ D) = ℕ , ℕ , D
fullyReducible' (ne' K D neK K≡K) = K , ne neK , D
fullyReducible' (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ▹ G , Π , D
fullyReducible' (emb 0<1 [A]) = fullyReducible' [A]

fullyReducible : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
fullyReducible a with fundamental a
... | [Γ] , [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      B , whnfB , D = fullyReducible' (proj₁ ([A] ⊢Γ [id]))
  in  B , whnfB
  ,   PE.subst (λ x → _ ⊢ x :⇒*: B) (substIdEq _) D

fullyReducibleTerm' : ∀ {a A Γ l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
fullyReducibleTerm' (U x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
fullyReducibleTerm' (ℕ x) (ℕₜ n d n≡n natN prop) =
  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
fullyReducibleTerm' (ne x) (neₜ k d (neNfₜ neK ⊢k k≡k)) = k , ne neK , d
fullyReducibleTerm' (Π x) (Πₜ f d funcF f≡f [f] [f]₁) = f , functionWhnf funcF , d
fullyReducibleTerm' (emb 0<1 [A]) [a] = fullyReducibleTerm' [A] [a]

fullyReducibleTerm : ∀ {a A Γ} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
fullyReducibleTerm a with fundamentalTerm a
... | [Γ] , [A] , [a] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
      b , whnfB , d = fullyReducibleTerm' (proj₁ ([A] ⊢Γ [id])) (proj₁ ([a] ⊢Γ [id]))
  in  b , whnfB
  ,   PE.subst₂ (λ x y → _ ⊢ x :⇒*: b ∷ y) (substIdEq _) (substIdEq _) d
