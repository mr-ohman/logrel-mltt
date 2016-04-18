module Definition.Untyped.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Definition.Untyped
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)

subst-test : {x : Term} → lam (var zero) [ x ] ≡ lam (var zero)
subst-test = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b
        → f x u a ≡ f y v b
cong₃ f refl refl refl = refl

idSubst-lemma-var : (m n : Nat) → subst (idSubst n) (var m) ≡ var m
idSubst-lemma-var m zero = refl
idSubst-lemma-var zero (suc zero) = refl
idSubst-lemma-var (suc m) (suc zero) = {!!}  -- var m ≡ var (suc m)
idSubst-lemma-var m (suc (suc n)) = {!!}

idSubst-lemma : (t : Term) (n : Nat) → subst (idSubst n) t ≡ t
idSubst-lemma U n = refl
idSubst-lemma (Π t ▹ t₁) n = cong₂ Π_▹_ (idSubst-lemma t n) (idSubst-lemma t₁ (suc n))
idSubst-lemma ℕ n = refl
idSubst-lemma (var x) n = idSubst-lemma-var x n
idSubst-lemma (lam t) n = cong lam (idSubst-lemma t (suc n))
idSubst-lemma (t ∘ t₁) n = cong₂ _∘_ (idSubst-lemma t n) (idSubst-lemma t₁ n)
idSubst-lemma zero n = refl
idSubst-lemma (suc t) n = cong suc (idSubst-lemma t n)
idSubst-lemma (natrec t t₁ t₂) n = cong₃ natrec (idSubst-lemma t (suc n))
                                                (idSubst-lemma t₁ n)
                                                (idSubst-lemma t₂ n)

idSubst-lemma₀ : (t : Term) → subst [] t ≡ t
idSubst-lemma₀ t = idSubst-lemma t zero
