module Definition.LogicalRelation.Properties.Neutral where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Soundness
open import Definition.LogicalRelation.Properties.Symmetry

open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as PE


neu : ∀ {l Γ A} (neA : Neutral A) → Γ ⊢ A → Γ ⊩⟨ l ⟩ A
neu neA A = ne (ne _ (idRed:*: A) neA)

neuEq' : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neB : Neutral B)
       → Γ ⊢ A :≡: B → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq' (noemb (ne K D neK)) neB (A , B , A≡B) =
  ne[ _ , idRed:*: B , neB , trans (sym (subset* (red D))) A≡B ]
neuEq' (emb 0<1 x) neB A:≡:B = neuEq' x neB A:≡:B

neuEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A :≡: B
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB A:≡:B =
  irrelevanceEq (ne-intr (ne-elim [A] neA))
                [A]
                (neuEq' (ne-elim [A] neA) neB A:≡:B)

mutual
  neuTerm : ∀ {l Γ A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (U (U .⁰ 0<1 ⊢Γ)) neN n = n , neu neN (univ n)
  neuTerm (ℕ (ℕ D)) neN n =
    let A≡ℕ = subset* (red D)
    in  ℕ[ _ , idRedTerm:*: (conv n A≡ℕ) , ne neN , conv n A≡ℕ ]
  neuTerm (ne (ne K D neK)) neN n = n
  neuTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) neN n = n
    , (λ ρ ⊢Δ [a] [b] [a≡b] →
      let A≡ΠFG = subset* (red D)
          ρA≡ρΠFG = wkEq ρ ⊢Δ (subset* (red D))
          G[a]≡G[b] = soundnessEq ([G] ρ ⊢Δ [b])
                                  (symEq ([G] ρ ⊢Δ [a]) ([G] ρ ⊢Δ [b])
                                         (G-ext ρ ⊢Δ [a] [b] [a≡b]))
          a = soundnessTerm ([F] ρ ⊢Δ) [a]
          b = soundnessTerm ([F] ρ ⊢Δ) [b]
          a≡b = soundnessTermEq ([F] ρ ⊢Δ) [a≡b]
          ρn = conv (wkTerm ρ ⊢Δ n) ρA≡ρΠFG
          neN∘a = _∘_ (wkNeutral (toWk ρ) neN)
          neN∘b = _∘_ (wkNeutral (toWk ρ) neN)
      in  neuEqTerm ([G] ρ ⊢Δ [a]) neN∘a neN∘b
                       ( (ρn ∘ a)
                       , (conv (ρn ∘ b) G[a]≡G[b])
                       , app-cong (refl ρn) a≡b))
    , (λ ρ ⊢Δ [a] → let ρA≡ρΠFG = wkEq ρ ⊢Δ (subset* (red D))
                        a = soundnessTerm ([F] ρ ⊢Δ) [a]
                    in  neuTerm ([G] ρ ⊢Δ [a]) (_∘_ (wkNeutral (toWk ρ) neN))
                                (conv (wkTerm ρ ⊢Δ n) ρA≡ρΠFG ∘ a))
  neuTerm (emb {l< = 0<1} x) neN n = neuTerm x neN n

  neuEqTerm : ∀ {l Γ A n n'} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN' : Neutral n')
            → Γ ⊢ n :≡: n' ∷ A → Γ ⊩⟨ l ⟩ n ≡ n' ∷ A / [A]
  neuEqTerm (U (U .⁰ 0<1 ⊢Γ)) neN neN' (n , n' , n≡n') =
    let [n]  = neu neN  (univ n)
        [n'] = neu neN' (univ n')
    in  U[ n , n' , n≡n' , [n] , [n']
         , neuEq [n] neN neN' (univ n , univ n' , univ n≡n') ]
  neuEqTerm (ℕ (ℕ D)) neN neN' (n , n' , n≡n') =
    let A≡ℕ = subset* (red D)
    in  ℕ≡[ _ , _ , idRedTerm:*: (conv n A≡ℕ) , idRedTerm:*: (conv n' A≡ℕ)
          , conv n≡n' A≡ℕ , ne neN neN' , conv n≡n' A≡ℕ ]
  neuEqTerm (ne (ne K D neK)) neN neN' (n , n' , n≡n') = n≡n'
  neuEqTerm (Π (Π F G D ⊢F ⊢G [F] [G] G-ext)) neN neN' (n , n' , n≡n') =
    let [ΠFG] = Π (Π F G D ⊢F ⊢G [F] [G] G-ext)
    in  n≡n' , neuTerm [ΠFG] neN n , neuTerm [ΠFG] neN' n'
     ,  (λ ρ ⊢Δ [a] →
        let A≡ΠFG = subset* (red D)
            ρA≡ρΠFG = wkEq ρ ⊢Δ (subset* (red D))
            ρn = wkTerm ρ ⊢Δ n
            ρn' = wkTerm ρ ⊢Δ n'
            a = soundnessTerm ([F] ρ ⊢Δ) [a]
            neN∙a   = _∘_ (wkNeutral (toWk ρ) neN)
            neN'∙a' = _∘_ (wkNeutral (toWk ρ) neN')
        in  neuEqTerm ([G] ρ ⊢Δ [a]) neN∙a neN'∙a'
                      ( (conv ρn  ρA≡ρΠFG ∘ a)
                      , (conv ρn' ρA≡ρΠFG ∘ a)
                      , app-cong (wkEqTerm ρ ⊢Δ (conv n≡n' A≡ΠFG)) (refl a)))
  neuEqTerm (emb {l< = 0<1} x) neN neN' n:≡:n' = neuEqTerm x neN neN' n:≡:n'
