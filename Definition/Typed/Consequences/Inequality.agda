{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.Typed.Consequences.Inequality where

open import Definition.Untyped hiding (U≢ne; ℕ≢ne; B≢ne)
open import Definition.Typed
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic

open import Tools.Product
open import Tools.Empty


A≢B : ∀ {A B Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
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

U≢ℕ′ : ∀ {Γ B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {B Γ} → Γ ⊢ B ⇒* ℕ → Γ ⊢ U ≡ B → ⊥
U≢ℕ-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ : ∀ {Γ} → Γ ⊢ U ≡ ℕ → ⊥
U≢ℕ U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U and Empty
U≢Empty′ : ∀ {Γ B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Empty] : Γ ⊩Empty B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Emptyᵣ [Empty]) → ⊥
U≢Empty′ a b ()

U≢Empty-red : ∀ {B Γ} → Γ ⊢ B ⇒* Empty → Γ ⊢ U ≡ B → ⊥
U≢Empty-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩Empty B) Uᵣ Emptyᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                U≢Empty′

U≢Emptyⱼ : ∀ {Γ} → Γ ⊢ U ≡ Empty → ⊥
U≢Emptyⱼ U≡Empty =
  let _ , ⊢Empty = syntacticEq U≡Empty
  in  U≢Empty-red (id ⊢Empty) U≡Empty

-- U and Unit
U≢Unit′ : ∀ {Γ B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Unit] : Γ ⊩Unit B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Unitᵣ [Unit]) → ⊥
U≢Unit′ a b ()

U≢Unit-red : ∀ {B Γ} → Γ ⊢ B ⇒* Unit → Γ ⊢ U ≡ B → ⊥
U≢Unit-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩Unit B) Uᵣ Unitᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                U≢Unit′

U≢Unitⱼ : ∀ {Γ} → Γ ⊢ U ≡ Unit → ⊥
U≢Unitⱼ U≡Unit =
  let _ , ⊢Unit = syntacticEq U≡Unit
  in  U≢Unit-red (id ⊢Unit) U≡Unit

-- ℕ and Empty

ℕ≢Empty′ : ∀ {Γ B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Empty] : Γ ⊩Empty B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Emptyᵣ [Empty]) → ⊥
ℕ≢Empty′ a b ()

ℕ≢Empty-red : ∀ {B Γ} → Γ ⊢ B ⇒* Empty → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Empty-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Empty B) ℕᵣ Emptyᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                ℕ≢Empty′

ℕ≢Emptyⱼ : ∀ {Γ} → Γ ⊢ ℕ ≡ Empty → ⊥
ℕ≢Emptyⱼ ℕ≡Empty =
  let _ , ⊢Empty = syntacticEq ℕ≡Empty
  in  ℕ≢Empty-red (id ⊢Empty) ℕ≡Empty

-- ℕ and Unit

ℕ≢Unit′ : ∀ {Γ B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Unit] : Γ ⊩Unit B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Unitᵣ [Unit]) → ⊥
ℕ≢Unit′ a b ()

ℕ≢Unit-red : ∀ {B Γ} → Γ ⊢ B ⇒* Unit → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Unit-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Unit B) ℕᵣ Unitᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                ℕ≢Unit′

ℕ≢Unitⱼ : ∀ {Γ} → Γ ⊢ ℕ ≡ Unit → ⊥
ℕ≢Unitⱼ ℕ≡Unit =
  let _ , ⊢Unit = syntacticEq ℕ≡Unit
  in  ℕ≢Unit-red (id ⊢Unit) ℕ≡Unit

-- Empty and Unit

Empty≢Unit′ : ∀ {Γ B l l'}
           ([Empty] : Γ ⊩Empty Empty)
           ([Unit] : Γ ⊩Unit B)
           → ShapeView Γ l l' _ _ (Emptyᵣ [Empty]) (Unitᵣ [Unit]) → ⊥
Empty≢Unit′ a b ()

Empty≢Unit-red : ∀ {B Γ} → Γ ⊢ B ⇒* Unit → Γ ⊢ Empty ≡ B → ⊥
Empty≢Unit-red D = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩Unit B) Emptyᵣ Unitᵣ
                (λ x → extractMaybeEmb (Empty-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                Empty≢Unit′

Empty≢Unitⱼ : ∀ {Γ} → Γ ⊢ Empty ≡ Unit → ⊥
Empty≢Unitⱼ Empty≡Unit =
  let _ , ⊢Unit = syntacticEq Empty≡Unit
  in  Empty≢Unit-red (id ⊢Unit) Empty≡Unit

-- Universe and Π

U≢Π′ : ∀ {B Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Π] : Γ ⊩′⟨ l′ ⟩B⟨ BΠ ⟩ B)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (Bᵣ BΠ [Π]) → ⊥
U≢Π′ a b ()

U≢Π-red : ∀ {B F G Γ} → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ U ≡ B → ⊥
U≢Π-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U)
                (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΠ ⟩ A) Uᵣ (Bᵣ BΠ)
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (B-elim′ BΠ D x))
                U≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢Π : ∀ {F G Γ} → Γ ⊢ U ≡ Π F ▹ G → ⊥
U≢Π U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π

U≢ne′ : ∀ {K Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Uᵣ [U]) (ne [K]) → ⊥
U≢ne′ a b ()

U≢ne-red : ∀ {B K Γ} → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ U ≡ B → ⊥
U≢ne-red D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ U ≡ K → ⊥
U≢ne neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢Π′ : ∀ {A B Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([Π] : Γ ⊩′⟨ l′ ⟩B⟨ BΠ ⟩ B)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (Bᵣ BΠ [Π]) → ⊥
ℕ≢Π′ a b ()

ℕ≢Π-red : ∀ {A B F G Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ A ≡ B → ⊥
ℕ≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΠ ⟩ A) ℕᵣ (Bᵣ BΠ)
                   (λ x → extractMaybeEmb (ℕ-elim′ D x))
                   (λ x → extractMaybeEmb (B-elim′ BΠ D′ x))
                   ℕ≢Π′

-- ℕ and Π F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢Π : ∀ {F G Γ} → Γ ⊢ ℕ ≡ Π F ▹ G → ⊥
ℕ≢Π ℕ≡Π =
  let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
  in  ℕ≢Π-red (id ⊢ℕ) (id ⊢Π) ℕ≡Π

-- Empty and Π
Empty≢Π′ : ∀ {A B Γ l l′}
       ([Empty] : Γ ⊩Empty A)
       ([Π] : Γ ⊩′⟨ l′ ⟩B⟨ BΠ ⟩ B)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (Bᵣ BΠ [Π]) → ⊥
Empty≢Π′ a b ()

Empty≢Π-red : ∀ {A B F G Γ} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ A ≡ B → ⊥
Empty≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΠ ⟩ A) Emptyᵣ (Bᵣ BΠ)
                   (λ x → extractMaybeEmb (Empty-elim′ D x))
                   (λ x → extractMaybeEmb (B-elim′ BΠ D′ x))
                   Empty≢Π′

Empty≢Πⱼ : ∀ {F G Γ} → Γ ⊢ Empty ≡ Π F ▹ G → ⊥
Empty≢Πⱼ Empty≡Π =
  let ⊢Empty , ⊢Π = syntacticEq Empty≡Π
  in  Empty≢Π-red (id ⊢Empty) (id ⊢Π) Empty≡Π

-- Unit and Π
Unit≢B′ : ∀ {A B Γ l l′} W
       ([Unit] : Γ ⊩Unit A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (Bᵣ W [W]) → ⊥
Unit≢B′ W a b ()

Unit≢B-red : ∀ {A B F G Γ} W → Γ ⊢ A ⇒* Unit → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
Unit≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩Unit A)
                    (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Unitᵣ (Bᵣ W)
                    (λ x → extractMaybeEmb (Unit-elim′ D x))
                    (λ x → extractMaybeEmb (B-elim′ W D′ x))
                    (Unit≢B′ W)

Unit≢Bⱼ : ∀ {F G Γ} W → Γ ⊢ Unit ≡ ⟦ W ⟧ F ▹ G → ⊥
Unit≢Bⱼ W Unit≡W =
  let ⊢Unit , ⊢W = syntacticEq Unit≡W
  in  Unit≢B-red W (id ⊢Unit) (id ⊢W) Unit≡W

ℕ≢ne′ : ∀ {A K Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
ℕ≢ne neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- Empty and neutral
Empty≢ne′ : ∀ {A K Γ l l′}
       ([Empty] : Γ ⊩Empty A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()

Empty≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Empty≢ne′

Empty≢neⱼ : ∀ {K Γ} → Neutral K → Γ ⊢ Empty ≡ K → ⊥
Empty≢neⱼ neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

-- Unit and neutral
Unit≢ne′ : ∀ {A K Γ l l′}
       ([Unit] : Γ ⊩Unit A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (ne [K]) → ⊥
Unit≢ne′ a b ()

Unit≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* Unit → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Unit≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Unit A) (λ Γ l B → Γ ⊩ne B) Unitᵣ ne
                        (λ x → extractMaybeEmb (Unit-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Unit≢ne′

Unit≢neⱼ : ∀ {K Γ} → Neutral K → Γ ⊢ Unit ≡ K → ⊥
Unit≢neⱼ neK Unit≡K =
  let ⊢Unit , ⊢K = syntacticEq Unit≡K
  in  Unit≢ne-red (id ⊢Unit) (id ⊢K) neK Unit≡K

B≢ne′ : ∀ {A K Γ l l′} W
       ([W] : Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Bᵣ W [W]) (ne [K]) → ⊥
B≢ne′ W a b ()

B≢ne-red : ∀ {A B F G K Γ} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ B ⇒* K → Neutral K
     → Γ ⊢ A ≡ B → ⊥
B≢ne-red W D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
                          (λ Γ l B → Γ ⊩ne B) (Bᵣ W) ne
                          (λ x → extractMaybeEmb (B-elim′ W D x))
                          (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                          (B≢ne′ W)

-- ⟦ W ⟧ F ▹ G and K for any F and G and neutral K cannot be judgmentally equal.
B≢ne : ∀ {F G K Γ} W → Neutral K → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ K → ⊥
B≢ne W neK W≡K =
  let ⊢W , ⊢K = syntacticEq W≡K
  in  B≢ne-red W (id ⊢W) (id ⊢K) neK W≡K

Π≢ne : ∀ {F G K Γ} → _
Π≢ne {F} {G} {K} {Γ} = B≢ne {F} {G} {K} {Γ} BΠ
Σ≢ne : ∀ {F G K Γ} → _
Σ≢ne {F} {G} {K} {Γ} = B≢ne {F} {G} {K} {Γ} BΣ
