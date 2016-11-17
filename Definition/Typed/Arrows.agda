module Definition.Typed.Arrows where

-- This module might not be solvable without Π-injectivity or adjustments to type judgements.

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Tools.Context

open import Tools.Product

wfTail : ∀ {Γ A} → ⊢ Γ ∙ A → ⊢ Γ
wfTail (⊢Γ ∙ A) = ⊢Γ

mutual
  _[_]ₜ : ∀ {Γ A B t} → Γ ∙ A ⊢ B → Γ ⊢ t ∷ A → Γ ⊢ B [ t ]
  ℕ x [ t₁ ]ₜ = ℕ (wfTail x)
  U x [ t₁ ]ₜ = U (wfTail x)
  Π A₁ ▹ A₂ [ t₁ ]ₜ = Π (A₁ [ t₁ ]ₜ) ▹ {!lift?!}
  univ x [ t₁ ]ₜ = univ (x [ t₁ ]Termₜ)

  _[_]Termₜ : ∀ {Γ A B t u} → Γ ∙ A ⊢ t ∷ B → Γ ⊢ u ∷ A → Γ ⊢ t [ u ] ∷ B [ u ]
  ℕ x [ u₁ ]Termₜ = ℕ (wfTail x)
  Π t ▹ t₁ [ u₁ ]Termₜ = {!!}
  var x₁ x₂ [ u₁ ]Termₜ = {!x₂!}
  lam x t₁ [ u₁ ]Termₜ = lam (x [ u₁ ]ₜ) {!!}
  (t ∘ t₁) [ u₁ ]Termₜ = {!!}
  zero x [ u₁ ]Termₜ = zero (wfTail x)
  suc t [ u₁ ]Termₜ = suc (t [ u₁ ]Termₜ)
  natrec x t t₁ t₂ [ u₁ ]Termₜ = {!!}
  conv t₁ x [ u₁ ]Termₜ = conv (t₁ [ u₁ ]Termₜ) (x [ refl u₁ ]Eqₜ)

  _[_]Eqₜ' : ∀ {Γ A C t u} → Γ ∙ C ⊢ A → Γ ⊢ t ≡ u ∷ C → Γ ⊢ A [ t ] ≡ A [ u ]
  _[_]Eqₜ' = {!!}

  _[_]Eqₜ : ∀ {Γ A B C t u} → Γ ∙ C ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ C → Γ ⊢ A [ t ] ≡ B [ u ]
  univ x [ t₁ ]Eqₜ = univ (x [ t₁ ]EqTermₜ)
  refl x [ t ]Eqₜ = {!!}
  sym A≡B [ t₁ ]Eqₜ = sym (A≡B [ (sym t₁) ]Eqₜ)
  trans A≡B A≡B₁ [ t₁ ]Eqₜ = trans (A≡B [ t₁ ]Eqₜ) (A≡B₁ [ trans (sym t₁) t₁ ]Eqₜ)
  Π-cong x A≡B A≡B₁ [ t₁ ]Eqₜ = Π-cong {!_[_]ₜ!} (A≡B [ t₁ ]Eqₜ) {!!}

  _[_]EqTermₜ : ∀ {Γ A B t u a b} → Γ ∙ A ⊢ a ≡ b ∷ B → Γ ⊢ t ≡ u ∷ A → Γ ⊢ a [ t ] ≡ b [ u ] ∷ B [ t ]
  _[_]EqTermₜ = {!!}

  conSubst : ∀ {Γ A B C} → Γ ⊢ A ≡ B → Γ ∙ A ⊢ C → Γ ∙ B ⊢ C
  conSubst A≡B (ℕ (x ∙ x₁)) = ℕ (x ∙ (proj₂ (eq A≡B)))
  conSubst A≡B (U x) = {!!}
  conSubst A≡B (Π C ▹ C₁) = {!!}
  conSubst A≡B (univ x) = {!!}

  eq : ∀ {Γ A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
  eq (univ x) = let a , b = eqTerm x
                in univ a , univ b
  eq (refl x) = x , x
  eq (sym e) = swap (eq e)
  eq (trans e e₁) = let a , b = eq e
                        c , d = eq e₁
                    in  a , d
  eq (Π-cong x e e₁) = let a , b = eq e
                           c , d = eq e₁
                       in  Π a ▹ c , Π b ▹ conSubst e d

  eqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  eqTerm (refl x) = x , x
  eqTerm (sym t₂) = swap (eqTerm t₂)
  eqTerm (trans t₁ t₂) = let a , b = eqTerm t₁
                             c , d = eqTerm t₂
                         in a , d
  eqTerm (conv t₁ x) = let a , b = eqTerm t₁
                       in  conv a x , conv b x
  eqTerm (Π-cong x t t₁) = let a , b = eqTerm t
                               c , d = eqTerm t₁
                           in  Π a ▹ c , Π b ▹ {!d!}
  eqTerm (app-cong t t₁) = let a , b = eqTerm t
                               c , d = eqTerm t₁
                           in  a ∘ c , conv (b ∘ d) ({!!} [ sym t₁ ]Eqₜ')
  eqTerm (β-red e x x₁) = ((lam e x) ∘ x₁) , x [ x₁ ]Termₜ
  eqTerm (fun-ext e x x₁ t) = x , x₁
  eqTerm (natrec-cong e x t t₁) = let a  , b  = eq e
                                      a₁ , b₁ = eqTerm x
                                      a₂ , b₂ = eqTerm t
                                      a₃ , b₃ = eqTerm t₁
                                  in  natrec a a₁ a₂ a₃ , conv (natrec b {!b₁!} {!b₂!} b₃) ((sym e) [ (sym t₁) ]Eqₜ)
  eqTerm (natrec-zero x x₁ x₂) = (natrec x x₁ x₂ (zero (wfTerm x₁))) , x₁
  eqTerm (natrec-suc x x₁ x₂ x₃) = (natrec x₁ x₂ x₃ (suc x)) , conv ((x₃ ∘ x) ∘ (natrec x₁ x₂ x₃ x)) {!!}
  eqTerm (suc-cong t) = let a , b = eqTerm t
                        in  suc a , suc b

  typeOfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ A
  typeOfTerm (var x₁ x₂) = {!!}
  typeOfTerm (ℕ x) = U x
  typeOfTerm (Π t ▹ t₁) = U (wfTerm t)
  typeOfTerm (lam y t₁) with wfTerm t₁
  typeOfTerm (lam y t₁) | x ∙ x₁ = Π x₁ ▹ typeOfTerm t₁
  typeOfTerm (t ∘ t₁) = {!!}
  typeOfTerm (zero x) = ℕ x
  typeOfTerm (suc t) = typeOfTerm t
  typeOfTerm (natrec x t t₁ n) = x [ n ]ₜ
  typeOfTerm (conv t₁ x) = proj₂ (eq x)

  typeOfTermEq : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A
  typeOfTermEq t≡u = {!!}
