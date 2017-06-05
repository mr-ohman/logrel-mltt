{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Inequality where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Soundness
open import Definition.LogicalRelation.Fundamental
open import Definition.Typed.Consequences.Syntactic

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


A≢B : ∀ {A B Γ} (_⊩'⟨_⟩A_ _⊩'⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {l} → Γ ⊩'⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
      (B-intr : ∀ {l} → Γ ⊩'⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A → ∃ λ l' → Γ ⊩'⟨ l' ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B → ∃ λ l' → Γ ⊩'⟨ l' ⟩B B)
      (A≢B' : ∀ {l l'} ([A] : Γ ⊩'⟨ l ⟩A A) ([B] : Γ ⊩'⟨ l' ⟩B B)
            → Tactic Γ l l' A B (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B' A≡B with fundamentalEq A≡B
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B' A≡B | [Γ] , [A] , [B] , [A≡B] =
  let [idA] = soundness [Γ] [A]
      [idB] = soundness [Γ] [B]
      [idA≡B] = soundnessEq {A} {B} [Γ] [A] [A≡B]
      _ , [A]' = A-elim ([idA])
      _ , [B]' = B-elim ([idB])
      [idA≡B]' = irrelevanceEq [idA] (A-intr [A]') [idA≡B]
  in  A≢B' [A]' [B]' (goodCases (A-intr [A]') (B-intr [B]') [idA≡B]')

U≢ℕ' : ∀ {Γ B l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ B)
     → Tactic Γ l l' _ _ (U [U]) (ℕ [ℕ]) → ⊥
U≢ℕ' a b ()

U≢ℕ-red : ∀ {B Γ} → Γ ⊢ B ⇒* ℕ → Γ ⊢ U ≡ B → ⊥
U≢ℕ-red D = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) U ℕ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim' D x))
                U≢ℕ'

U≢ℕ : ∀ {Γ} → Γ ⊢ U ≡ ℕ → ⊥
U≢ℕ U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

U≢Π' : ∀ {B Γ l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l' B)
     → Tactic Γ l l' _ _ (U [U]) (Π [Π]) → ⊥
U≢Π' a b ()

U≢Π-red : ∀ {B F G Γ} → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ U ≡ B → ⊥
U≢Π-red D = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (_⊩'⟨_⟩Π_ {{eqRelInstance}}) U Π
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Π-elim' D x))
                U≢Π'

U≢Π : ∀ {F G Γ} → Γ ⊢ U ≡ Π F ▹ G → ⊥
U≢Π U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π

U≢ne' : ∀ {K Γ l l'}
       ([U] : Γ ⊩'⟨ l ⟩U)
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (U [U]) (ne [K]) → ⊥
U≢ne' a b ()

U≢ne-red : ∀ {B K Γ} → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ U ≡ B → ⊥
U≢ne-red D neK = A≢B (λ Γ l A → Γ ⊩'⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B) U ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim' D neK x))
                     U≢ne'

U≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ U ≡ K → ⊥
U≢ne neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢Π' : ∀ {A B Γ l l'}
       ([ℕ] : Γ ⊩ℕ A)
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l' B)
     → Tactic Γ l l' _ _ (ℕ [ℕ]) (Π [Π]) → ⊥
ℕ≢Π' a b ()

ℕ≢Π-red : ∀ {A B F G Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ A ≡ B → ⊥
ℕ≢Π-red D D' = A≢B (λ Γ l A → Γ ⊩ℕ A) (_⊩'⟨_⟩Π_ {{eqRelInstance}}) ℕ Π
                   (λ x → extractMaybeEmb (ℕ-elim' D x))
                   (λ x → extractMaybeEmb (Π-elim' D' x))
                   ℕ≢Π'

ℕ≢Π : ∀ {F G Γ} → Γ ⊢ ℕ ≡ Π F ▹ G → ⊥
ℕ≢Π ℕ≡Π =
  let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
  in  ℕ≢Π-red (id ⊢ℕ) (id ⊢Π) ℕ≡Π

ℕ≢ne' : ∀ {A K Γ l l'}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (ℕ [ℕ]) (ne [K]) → ⊥
ℕ≢ne' a b ()

ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
ℕ≢ne-red D D' neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕ ne
                        (λ x → extractMaybeEmb (ℕ-elim' D x))
                        (λ x → extractMaybeEmb (ne-elim' D' neK x))
                        ℕ≢ne'

ℕ≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
ℕ≢ne neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

Π≢ne' : ∀ {A K Γ l l'}
       ([Π] : _⊩'⟨_⟩Π_ {{eqRelInstance}} Γ l A)
       ([K] : Γ ⊩ne K)
     → Tactic Γ l l' _ _ (Π [Π]) (ne [K]) → ⊥
Π≢ne' a b ()

Π≢ne-red : ∀ {A B F G K Γ} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* K → Neutral K
     → Γ ⊢ A ≡ B → ⊥
Π≢ne-red D D' neK = A≢B (_⊩'⟨_⟩Π_ {{eqRelInstance}}) (λ Γ l B → Γ ⊩ne B) Π ne
                        (λ x → extractMaybeEmb (Π-elim' D x))
                        (λ x → extractMaybeEmb (ne-elim' D' neK x))
                        Π≢ne'

Π≢ne : ∀ {F G K Γ} → Neutral K → Γ ⊢ Π F ▹ G ≡ K → ⊥
Π≢ne neK Π≡K =
  let ⊢Π , ⊢K = syntacticEq Π≡K
  in  Π≢ne-red (id ⊢Π) (id ⊢K) neK Π≡K
