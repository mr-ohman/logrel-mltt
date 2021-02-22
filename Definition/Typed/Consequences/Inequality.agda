{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Inequality where

open import Definition.Untyped hiding (U≢ne; ℕ≢ne; B≢ne; U≢B; ℕ≢B)
open import Definition.Typed
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic

open import Tools.Nat
open import Tools.Product
open import Tools.Empty

private
  variable
    n : Nat
    Γ : Con Term n

A≢B : ∀ {A B Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term n → TypeLevel → Term n → Set)
      (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
      (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B)
      (A≢B′ : ∀ {l l′} ([A] : Γ ⊩′⟨ l ⟩A A) ([B] : Γ ⊩′⟨ l′ ⟩B B)
            → ShapeView Γ l l′ A B (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B with reducibleEq A≡B
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B | [A] , [B] , [A≡B] =
  let _ , [A]′ = A-elim ([A])
      _ , [B]′ = B-elim ([B])
      [A≡B]′ = irrelevanceEq [A] (A-intr [A]′) [A≡B]
  in  A≢B′ [A]′ [B]′ (goodCases (A-intr [A]′) (B-intr [B]′) [A≡B]′)

U≢ℕ′ : ∀ {B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {B} → Γ ⊢ B ⇒* ℕ → Γ ⊢ U ≡ B → ⊥
U≢ℕ-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ : Γ ⊢ U ≡ ℕ → ⊥
U≢ℕ U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U and Empty
U≢Empty′ : ∀ {B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Empty] : Γ ⊩Empty B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Emptyᵣ [Empty]) → ⊥
U≢Empty′ a b ()

U≢Empty-red : ∀ {B} → Γ ⊢ B ⇒* Empty → Γ ⊢ U ≡ B → ⊥
U≢Empty-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩Empty B) Uᵣ Emptyᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                U≢Empty′

U≢Emptyⱼ : Γ ⊢ U ≡ Empty → ⊥
U≢Emptyⱼ U≡Empty =
  let _ , ⊢Empty = syntacticEq U≡Empty
  in  U≢Empty-red (id ⊢Empty) U≡Empty

-- U and Unit
U≢Unit′ : ∀ {B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Unit] : Γ ⊩Unit B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Unitᵣ [Unit]) → ⊥
U≢Unit′ a b ()

U≢Unit-red : ∀ {B} → Γ ⊢ B ⇒* Unit → Γ ⊢ U ≡ B → ⊥
U≢Unit-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩Unit B) Uᵣ Unitᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                U≢Unit′

U≢Unitⱼ : Γ ⊢ U ≡ Unit → ⊥
U≢Unitⱼ U≡Unit =
  let _ , ⊢Unit = syntacticEq U≡Unit
  in  U≢Unit-red (id ⊢Unit) U≡Unit

-- ℕ and Empty

ℕ≢Empty′ : ∀ {B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Empty] : Γ ⊩Empty B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Emptyᵣ [Empty]) → ⊥
ℕ≢Empty′ a b ()

ℕ≢Empty-red : ∀ {B} → Γ ⊢ B ⇒* Empty → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Empty-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Empty B) ℕᵣ Emptyᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                ℕ≢Empty′

ℕ≢Emptyⱼ : Γ ⊢ ℕ ≡ Empty → ⊥
ℕ≢Emptyⱼ ℕ≡Empty =
  let _ , ⊢Empty = syntacticEq ℕ≡Empty
  in  ℕ≢Empty-red (id ⊢Empty) ℕ≡Empty

-- ℕ and Unit

ℕ≢Unit′ : ∀ {B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Unit] : Γ ⊩Unit B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Unitᵣ [Unit]) → ⊥
ℕ≢Unit′ a b ()

ℕ≢Unit-red : ∀ {B} → Γ ⊢ B ⇒* Unit → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Unit-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Unit B) ℕᵣ Unitᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                ℕ≢Unit′

ℕ≢Unitⱼ : Γ ⊢ ℕ ≡ Unit → ⊥
ℕ≢Unitⱼ ℕ≡Unit =
  let _ , ⊢Unit = syntacticEq ℕ≡Unit
  in  ℕ≢Unit-red (id ⊢Unit) ℕ≡Unit

-- Empty and Unit

Empty≢Unit′ : ∀ {B l l'}
           ([Empty] : Γ ⊩Empty Empty)
           ([Unit] : Γ ⊩Unit B)
           → ShapeView Γ l l' _ _ (Emptyᵣ [Empty]) (Unitᵣ [Unit]) → ⊥
Empty≢Unit′ a b ()

Empty≢Unit-red : ∀ {B} → Γ ⊢ B ⇒* Unit → Γ ⊢ Empty ≡ B → ⊥
Empty≢Unit-red D = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩Unit B) Emptyᵣ Unitᵣ
                (λ x → extractMaybeEmb (Empty-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                Empty≢Unit′

Empty≢Unitⱼ : Γ ⊢ Empty ≡ Unit → ⊥
Empty≢Unitⱼ Empty≡Unit =
  let _ , ⊢Unit = syntacticEq Empty≡Unit
  in  Empty≢Unit-red (id ⊢Unit) Empty≡Unit

-- Universe and binding types

U≢B′ : ∀ {B l l′} W
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Bᵣ W [W]) → ⊥
U≢B′ W a b ()

U≢B-red : ∀ {B F G} W → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ U ≡ B → ⊥
U≢B-red W D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U)
                  (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Uᵣ (Bᵣ W)
                  (λ x → extractMaybeEmb (U-elim x))
                  (λ x → extractMaybeEmb (B-elim′ W D x))
                  (U≢B′ W)

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢B : ∀ {F G} W → Γ ⊢ U ≡ ⟦ W ⟧ F ▹ G → ⊥
U≢B W U≡W =
  let _ , ⊢W = syntacticEq U≡W
  in  U≢B-red W (id ⊢W) U≡W

U≢Π : ∀ {Γ : Con Term n} {F G} → _
U≢Π {Γ = Γ} {F} {G} = U≢B {Γ = Γ} {F} {G} BΠ
U≢Σ : ∀ {Γ : Con Term n} {F G} → _
U≢Σ {Γ = Γ} {F} {G} = U≢B {Γ = Γ} {F} {G} BΣ

U≢ne′ : ∀ {K l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (ne [K]) → ⊥
U≢ne′ a b ()

U≢ne-red : ∀ {B K} → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ U ≡ B → ⊥
U≢ne-red D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne : ∀ {K} → Neutral K → Γ ⊢ U ≡ K → ⊥
U≢ne neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢B′ : ∀ {A B l l′} W
       ([ℕ] : Γ ⊩ℕ A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (Bᵣ W [W]) → ⊥
ℕ≢B′ W a b ()

ℕ≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
ℕ≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                     (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) ℕᵣ (Bᵣ W)
                     (λ x → extractMaybeEmb (ℕ-elim′ D x))
                     (λ x → extractMaybeEmb (B-elim′ W D′ x))
                     (ℕ≢B′ W)

-- ℕ and B F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢B : ∀ {F G} W → Γ ⊢ ℕ ≡ ⟦ W ⟧ F ▹ G → ⊥
ℕ≢B W ℕ≡W =
  let ⊢ℕ , ⊢W = syntacticEq ℕ≡W
  in  ℕ≢B-red W (id ⊢ℕ) (id ⊢W) ℕ≡W

ℕ≢Π : ∀ {Γ : Con Term n} {F G} → _
ℕ≢Π {Γ = Γ} {F} {G} = ℕ≢B {Γ = Γ} {F} {G} BΠ
ℕ≢Σ : ∀ {Γ : Con Term n} {F G} → _
ℕ≢Σ {Γ = Γ} {F} {G} = ℕ≢B {Γ = Γ} {F} {G} BΣ

-- Empty and Π
Empty≢B′ : ∀ {A B l l′} W
       ([Empty] : Γ ⊩Empty A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (Bᵣ W [W]) → ⊥
Empty≢B′ W a b ()

Empty≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
Empty≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
                         (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Emptyᵣ (Bᵣ W)
                         (λ x → extractMaybeEmb (Empty-elim′ D x))
                         (λ x → extractMaybeEmb (B-elim′ W D′ x))
                         (Empty≢B′ W)

Empty≢Bⱼ : ∀ {F G} W → Γ ⊢ Empty ≡ ⟦ W ⟧ F ▹ G → ⊥
Empty≢Bⱼ W Empty≡W =
  let ⊢Empty , ⊢W = syntacticEq Empty≡W
  in  Empty≢B-red W (id ⊢Empty) (id ⊢W) Empty≡W

Empty≢Πⱼ : ∀ {Γ : Con Term n} {F G} → _
Empty≢Πⱼ {Γ = Γ} {F} {G} = Empty≢Bⱼ {Γ = Γ} {F} {G} BΠ
Empty≢Σⱼ : ∀ {Γ : Con Term n} {F G} → _
Empty≢Σⱼ {Γ = Γ} {F} {G} = Empty≢Bⱼ {Γ = Γ} {F} {G} BΣ

-- Unit and Π
Unit≢B′ : ∀ {A B l l′} W
       ([Unit] : Γ ⊩Unit A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (Bᵣ W [W]) → ⊥
Unit≢B′ W a b ()

Unit≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* Unit → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
Unit≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩Unit A)
                    (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Unitᵣ (Bᵣ W)
                    (λ x → extractMaybeEmb (Unit-elim′ D x))
                    (λ x → extractMaybeEmb (B-elim′ W D′ x))
                    (Unit≢B′ W)

Unit≢Bⱼ : ∀ {F G} W → Γ ⊢ Unit ≡ ⟦ W ⟧ F ▹ G → ⊥
Unit≢Bⱼ W Unit≡W =
  let ⊢Unit , ⊢W = syntacticEq Unit≡W
  in  Unit≢B-red W (id ⊢Unit) (id ⊢W) Unit≡W

Unit≢Πⱼ : ∀ {Γ : Con Term n} {F G} → _
Unit≢Πⱼ {Γ = Γ} {F} {G} = Unit≢Bⱼ {Γ = Γ} {F} {G} BΠ
Unit≢Σⱼ : ∀ {Γ : Con Term n} {F G} → _
Unit≢Σⱼ {Γ = Γ} {F} {G} = Unit≢Bⱼ {Γ = Γ} {F} {G} BΣ

ℕ≢ne′ : ∀ {A K l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne : ∀ {K} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
ℕ≢ne neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- Empty and neutral
Empty≢ne′ : ∀ {A K l l′}
       ([Empty] : Γ ⊩Empty A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()

Empty≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Empty≢ne′

Empty≢neⱼ : ∀ {K} → Neutral K → Γ ⊢ Empty ≡ K → ⊥
Empty≢neⱼ neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

-- Unit and neutral
Unit≢ne′ : ∀ {A K l l′}
       ([Unit] : Γ ⊩Unit A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (ne [K]) → ⊥
Unit≢ne′ a b ()

Unit≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* Unit → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Unit≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Unit A) (λ Γ l B → Γ ⊩ne B) Unitᵣ ne
                        (λ x → extractMaybeEmb (Unit-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Unit≢ne′

Unit≢neⱼ : ∀ {K} → Neutral K → Γ ⊢ Unit ≡ K → ⊥
Unit≢neⱼ neK Unit≡K =
  let ⊢Unit , ⊢K = syntacticEq Unit≡K
  in  Unit≢ne-red (id ⊢Unit) (id ⊢K) neK Unit≡K

B≢ne′ : ∀ {A K l l′} W
       ([W] : Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Bᵣ W [W]) (ne [K]) → ⊥
B≢ne′ W a b ()

B≢ne-red : ∀ {A B F G K} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ B ⇒* K → Neutral K
     → Γ ⊢ A ≡ B → ⊥
B≢ne-red W D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
                          (λ Γ l B → Γ ⊩ne B) (Bᵣ W) ne
                          (λ x → extractMaybeEmb (B-elim′ W D x))
                          (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                          (B≢ne′ W)

-- ⟦ W ⟧ F ▹ G and K for any W, F, G and neutral K cannot be judgmentally equal.
B≢ne : ∀ {F G K} W → Neutral K → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ K → ⊥
B≢ne W neK W≡K =
  let ⊢W , ⊢K = syntacticEq W≡K
  in  B≢ne-red W (id ⊢W) (id ⊢K) neK W≡K

Π≢ne : ∀ {Γ : Con Term n} {F G K} → _
Π≢ne {Γ = Γ} {F} {G} {K} = B≢ne {Γ = Γ} {F} {G} {K} BΠ
Σ≢ne : ∀ {Γ : Con Term n} {F G K} → _
Σ≢ne {Γ = Γ} {F} {G} {K} = B≢ne {Γ = Γ} {F} {G} {K} BΣ

-- Π and Σ
Π≢Σ′ : ∀ {A B l l′}
       ([A] : Γ ⊩′⟨ l ⟩B⟨ BΠ ⟩ A)
       ([B] : Γ ⊩′⟨ l′ ⟩B⟨ BΣ ⟩ B)
     → ShapeView Γ l l′ _ _ (Bᵣ BΠ [A]) (Bᵣ BΣ [B]) → ⊥
Π≢Σ′ a b ()

Π≢Σ-red : ∀ {A B F G H E} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* Σ H ▹ E → Γ ⊢ A ≡ B → ⊥
Π≢Σ-red D D′ = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΠ ⟩ A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΣ ⟩ A) (Bᵣ BΠ) (Bᵣ BΣ)
                   (λ x → extractMaybeEmb (B-elim′ BΠ D x))
                   (λ x → extractMaybeEmb (B-elim′ BΣ D′ x))
                   Π≢Σ′

Π≢Σ : ∀ {F G H E} → Γ ⊢ Π F ▹ G ≡ Σ H ▹ E → ⊥
Π≢Σ Π≡Σ =
  let ⊢Π , ⊢Σ = syntacticEq Π≡Σ
  in  Π≢Σ-red (id ⊢Π) (id ⊢Σ) Π≡Σ
