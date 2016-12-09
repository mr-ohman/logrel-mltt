module Definition.LogicalRelation.Consequences.Inequality where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


A≢B : {A B : Term} (_⊩'⟨_⟩A_ _⊩'⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {Γ l} → Γ ⊩'⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
      (B-intr : ∀ {Γ l} → Γ ⊩'⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B)
      (A-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ A → ∃ λ l' → Γ ⊩'⟨ l' ⟩A A)
      (B-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ B → ∃ λ l' → Γ ⊩'⟨ l' ⟩B B)
      (A≢B' : ∀ {Γ l l'} ([A] : Γ ⊩'⟨ l ⟩A A) ([B] : Γ ⊩'⟨ l' ⟩B B)
            → Tactic Γ l l' A B (A-intr [A]) (B-intr [B]) → ⊥)
    → ∀ {Γ} → Γ ⊢ A ≡ B → ⊥
A≢B _ _ A-intr B-intr A-elim B-elim A≢B' A≡B with fundamentalEq A≡B
A≢B _ _ A-intr B-intr A-elim B-elim A≢B' A≡B | [Γ] , [A] , [B] , [A≡B] =
  let ⊢Γ = soundContext [Γ]
      id = idSubstS [Γ]
      [idA] = proj₁ ([A] ⊢Γ id)
      [idB] = proj₁ ([B] ⊢Γ id)
      [idA≡B] = [A≡B] ⊢Γ id
      idAlemma = idSubst-lemma₀ _
      idBlemma = idSubst-lemma₀ _
      _ , [A]' = A-elim (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) idAlemma [idA])
      _ , [B]' = B-elim (PE.subst (λ x → _ ⊩⟨ _ ⟩ x) idBlemma [idB])
      [idA≡B]' = irrelevanceEq'' idAlemma idBlemma [idA] (A-intr [A]') [idA≡B]
  in  A≢B' [A]' [B]' (goodCases (A-intr [A]') (B-intr [B]') [idA≡B]')

U≢ℕ' : ∀ {Γ l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ ℕ)
     → Tactic Γ l l' _ _ (U [U]) (ℕ [ℕ]) → ⊥
U≢ℕ' a b ()

U≢ℕ : ∀ {Γ} → Γ ⊢ U ≡ ℕ → ⊥
U≢ℕ = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) U ℕ
          (λ x → extractMaybeEmb (U-elim x)) (λ x → extractMaybeEmb (ℕ-elim x))
          U≢ℕ'

U≢Π' : ∀ {F G Γ l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l' (Π F ▹ G))
     → Tactic Γ l l' _ _ (U [U]) (Π [Π]) → ⊥
U≢Π' a b ()

U≢Π : ∀ {F G Γ} → Γ ⊢ U ≡ Π F ▹ G → ⊥
U≢Π = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (_⊩'⟨_⟩Π_ {{eqRelInstance}}) U Π
          (λ x → extractMaybeEmb (U-elim x)) (λ x → extractMaybeEmb (Π-elim x))
          U≢Π'

U≢ne' : ∀ {K Γ l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (U [U]) (ne [K]) → ⊥
U≢ne' a b ()

U≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ U ≡ K → ⊥
U≢ne neK = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B) U ne
               (λ x → extractMaybeEmb (U-elim x)) (λ x → extractMaybeEmb (ne-elim x neK))
               U≢ne'

ℕ≢Π' : ∀ {F G Γ l l'}
       ([ℕ] : Γ ⊩ℕ ℕ)
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l' (Π F ▹ G))
     → Tactic Γ l l' _ _ (ℕ [ℕ]) (Π [Π]) → ⊥
ℕ≢Π' a b ()

ℕ≢Π : ∀ {F G Γ} → Γ ⊢ ℕ ≡ Π F ▹ G → ⊥
ℕ≢Π = A≢B (λ Γ l A → Γ ⊩ℕ A) (_⊩'⟨_⟩Π_ {{eqRelInstance}}) ℕ Π
          (λ x → extractMaybeEmb (ℕ-elim x)) (λ x → extractMaybeEmb (Π-elim x))
          ℕ≢Π'

ℕ≢ne' : ∀ {K Γ l l'}
       ([ℕ] : Γ ⊩ℕ ℕ)
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (ℕ [ℕ]) (ne [K]) → ⊥
ℕ≢ne' a b ()

ℕ≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
ℕ≢ne neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕ ne
          (λ x → extractMaybeEmb (ℕ-elim x)) (λ x → extractMaybeEmb (ne-elim x neK))
          ℕ≢ne'

Π≢ne' : ∀ {F G K Γ l l'}
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l (Π F ▹ G))
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (Π [Π]) (ne [K]) → ⊥
Π≢ne' a b ()

Π≢ne : ∀ {F G K Γ} → Neutral K → Γ ⊢ Π F ▹ G ≡ K → ⊥
Π≢ne neK = A≢B (_⊩'⟨_⟩Π_ {{eqRelInstance}}) (λ Γ l B → Γ ⊩ne B) Π ne
          (λ x → extractMaybeEmb (Π-elim x)) (λ x → extractMaybeEmb (ne-elim x neK))
          Π≢ne'
