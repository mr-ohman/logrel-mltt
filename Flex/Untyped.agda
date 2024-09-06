-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --safe #-}

module Flex.Untyped where

open import Tools.Empty
open import Tools.Unit
open import Tools.Bool
open import Data.Bool.Base using (T)
open import Tools.Fin
open import Tools.Nat
open import Tools.Sum hiding (id)
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE


infixr 5 _ne∷_
infixr 5 _nf∷_

infixl 30 _∙_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

data Con (A : Nat → Set) : Nat → Set where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private
  variable
    n m ℓ : Nat

-- Representation of sub terms using a list of binding levels

record KindArg : Set where
  constructor kindArg
  field
    bindLvl : Nat
    neu?    : Bool
open KindArg public

data GenTs (A : Nat → Set) (n : Nat) : List KindArg → Set where
  []  : GenTs A n []
  _∷_ : {b : KindArg} {bs : List KindArg}
        (t : A (bindLvl b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term

b0 b1 ne0 : KindArg
b0  = kindArg 0 false
b1  = kindArg 1 false
ne0 = kindArg 0 true

record DynKind : Set₁ where
  constructor dynKind
  field
    Kind     : Set
    KindArgs : Kind → List KindArg

open DynKind

-- Terms are indexed by its number of unbound variables and are either:
-- de Bruijn style variables or
-- generic terms, formed by their kind and sub terms

data Term (dk : DynKind) (n : Nat) : Set where
  var : (x : Fin n) → Term dk n
  gen : (k : Kind dk)
        (c : GenTs (Term dk) n (KindArgs dk k))
      → Term dk n


private
  variable
    dk dk′      : DynKind
    A F H t u v : Term dk n
    B E G       : Term dk (1+ n)


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

isElem : (dk : DynKind) → Kind dk → Bool
isElem dk i = L.any neu? (KindArgs dk i)

isConst : (dk : DynKind) → Kind dk → Bool
isConst dk i = not (isElem dk i)

TnotT : ∀ {b} → T b → T (not b) → ⊥
TnotT {false} Tb Tnb = Tb
TnotT {true} Tb Tnb = Tnb

data Construct {dk : DynKind} {n : Nat} : Term dk n → Set where
  cons : ∀ i {c} → T (isConst dk i) → Construct (gen i c)

mutual
  data Neutral {dk : DynKind} {n} : Term dk n → Set where
    var : ∀ x → Neutral (var x)
    gen : ∀ i {c} → T (isElem dk i) → GenTsNeu _ c → Neutral (gen i c)

  data GenTsNeu {dk n} : ∀ bs → GenTs (Term dk) n bs → Set where
    here  : ∀ {b bs t ts} → Neutral t → GenTsNeu (kindArg b true ∷ bs) (t ∷ ts)
    there : ∀ {b bs t ts} → GenTsNeu bs ts → GenTsNeu (b ∷ bs) (t ∷ ts)


data Whnf (t : Term dk n) : Set where
  cons : Construct t → Whnf t
  ne   : Neutral t → Whnf t

mutual
  data Nf (t : Term dk n) : Set where
    cons : NfConstruct t → Nf t
    ne   : NfNeutral t   → Nf t

  data NfConstruct {dk : DynKind} {n : Nat} : Term dk n → Set where
    cons : ∀ i {c m} → T (isConst dk i) → GenTsNf _ c m → NfConstruct (gen i c)

  data NfNeutral {dk : DynKind} {n} : Term dk n → Set where
    var : ∀ x → NfNeutral (var x)
    gen : ∀ i {c m} → T (isElem dk i) → GenTsNf _ c (1+ m) → NfNeutral (gen i c)

  data GenTsNf {dk n} : ∀ bs → GenTs (Term dk) n bs → Nat → Set where
    [] : GenTsNf [] [] 0
    _ne∷_ : ∀ {b bs t ts m} → NfNeutral t → GenTsNf bs ts m → GenTsNf (kindArg b true ∷ bs) (t ∷ ts) (1+ m)
    _nf∷_ : ∀ {b bs t ts m} → Nf t        → GenTsNf bs ts m → GenTsNf (b ∷ bs) (t ∷ ts) m

-- If the term at true in DynKind is DynKind and Neutral, then it is DynWhnf
-- if there are no trues, then it is DynWhnf


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.



-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

cons≢ne : Construct F → Neutral H → F PE.≢ H
cons≢ne (cons .i x) (gen i x₁ x₂) PE.refl = TnotT x₁ x


------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Nat → Nat → Set where
  id    : {n : Nat} → Wk n n                      -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- data WkLang : DynKind → DynKind → Set where
--   id    : ∀ {dk} → WkLang dk dk
--   step  : ∀ {d dk dk′} → WkLang dk dk′ → WkLang (d ∷ dk) dk′
--   lift  : ∀ {d dk dk′} → WkLang dk dk′ → WkLang (d ∷ dk) (d ∷ dk′)

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ Nat.zero = ρ
liftn ρ (1+ n)   = lift (liftn ρ n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List KindArg} (ρ : Wk m n) (c : GenTs (Term dk) n bs) → GenTs (Term dk) m bs
  wkGen ρ []                = []
  wkGen ρ (_∷_ {b = b} t c) = (wk (liftn ρ (bindLvl b)) t) ∷ (wkGen ρ c)

  wk : {m n : Nat} (ρ : Wk m n) (t : Term dk n) → Term dk m
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen k c) = gen k (wkGen ρ c)

-- wkLangVar : (ρ : WkLang dk dk′) (x : Fin (L.length dk′)) → Kind dk
-- wkLangVar id x            = x
-- wkLangVar (step ρ) x      = (wkLangVar ρ x) +1
-- wkLangVar (lift ρ) x0     = x0
-- wkLangVar (lift ρ) (x +1) = (wkLangVar ρ x) +1

-- blah : ∀ k (ρ : WkLang dk dk′) → L.lookup dk′ k PE.≡ L.lookup dk (wkLangVar ρ k)
-- blah k id = PE.refl
-- blah k (step ρ) = blah k ρ
-- blah x0 (lift ρ) = PE.refl
-- blah (_+1 k) (lift ρ) = blah k ρ

-- mutual
--   wkLangGen : {bs : List KindArg} (ρ : WkLang dk dk′) (c : GenTs (Term dk′) n bs) → GenTs (Term dk) n bs
--   wkLangGen ρ []                = []
--   wkLangGen ρ (_∷_ {b = b} t c) = (wkLang ρ t) ∷ (wkLangGen ρ c)

--   wkLang : (ρ : WkLang dk dk′) (t : Term dk′ n) → Term dk n
--   wkLang ρ (var x)   = var x
--   wkLang ρ (gen k c) rewrite blah k ρ = gen (wkLangVar ρ k) (wkLangGen ρ c)

-- wkLangCon : (ρ : WkLang dk dk′) (Γ : Con (Term dk′) n) → Con (Term dk) n
-- wkLangCon ρ ε = ε
-- wkLangCon ρ (Γ ∙ A) = wkLangCon ρ Γ ∙ wkLang ρ A

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term dk n → Term dk (1+ n)
wk1 = wk (step id)

-- Weakening of a neutral term.

mutual
  wkNeutral : ∀ ρ → Neutral t → Neutral {dk} {n} (wk ρ t)
  wkNeutral ρ (var n)     = var (wkVar ρ n)
  wkNeutral ρ (gen i {c} X Y) = gen i {wkGen ρ c} X (wkGenTsNeu ρ c Y)

  wkGenTsNeu : ∀ {n n′ bs} ρ c → GenTsNeu {dk} {n} bs c → GenTsNeu {dk} {n′} bs (wkGen ρ c)
  wkGenTsNeu {bs = []} ρ [] ()
  wkGenTsNeu {bs = kindArg b .true ∷ bs} ρ (t ∷ c) (here x) = here (wkNeutral (liftn ρ b) x)
  wkGenTsNeu {bs = kindArg b a ∷ bs} ρ (t ∷ c) (there y) = there (wkGenTsNeu ρ c y)

wkConst : ∀ ρ → Construct t → Construct {dk} {n} (wk ρ t)
wkConst ρ (cons i x) = cons i x

wkWhnf : ∀ ρ → Whnf t → Whnf {dk} {n} (wk ρ t)
wkWhnf ρ (cons x) = cons (wkConst ρ x)
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)


------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : DynKind → Nat → Nat → Set
Subst dk m n = Fin n → Term dk m

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst dk m (1+ n) → Term dk m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst dk m (1+ n) → Subst dk m n
tail σ x = σ (x +1)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst dk m n) (x : Fin n) → Term dk m
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst dk n n
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst dk m n → Subst dk (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst dk m n) → Subst dk (1+ m) (1+ n)
liftSubst σ x0     = var x0
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst dk k m → (n : Nat) → Subst dk (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst dk m n
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : {bs : List KindArg} (σ : Subst dk m n) (g : GenTs (Term dk) n bs) → GenTs (Term dk) m bs
  substGen σ  []      = []
  substGen σ (_∷_ {b = b} t ts) = subst (liftSubstn σ (bindLvl b)) t ∷ (substGen σ ts)

  subst : (σ : Subst dk m n) (t : Term dk n) → Term dk m
  subst σ (var x)   = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst dk m n → Term dk m → Subst dk m (1+ n)
consSubst σ t  x0    = t
consSubst σ t (x +1) = σ x

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term dk n → Subst dk n (1+ n)
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst dk ℓ m → Subst dk m n → Subst dk ℓ n
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk ℓ m → Subst dk m n → Subst dk ℓ n
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst dk ℓ m → Wk m n → Subst dk ℓ n
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term dk (1+ n)) (s : Term dk n) → Term dk n
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term dk (1+ n)) (s : Term dk (1+ n)) → Term dk (1+ n)
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


