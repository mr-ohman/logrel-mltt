{-# OPTIONS --without-K --safe #-}

module Tools.Reflection where

open import Reflection public
  hiding ( _≟_; _≟-Name_; _≟-Meta_; _≟-AbsTerm_
         ; _≟-AbsType_; _≟-ArgTerm_; _≟-ArgType_
         ; _≟-Args_; _≟-Clause_; _≟-Clauses_
         ; _≟-Sort_; _≟-Pattern_)
  renaming (Term to ATerm)
open import Reflection.Argument.Information public
  using (ArgInfo)
open import Reflection.Argument.Visibility public
  using (Visibility)
open import Reflection.Argument.Relevance public
  using (Relevance)
open import Reflection.Name public
  using (Name)
  renaming (_≟_ to _≟-Name_)
open import Reflection.Meta public
  using ()
  renaming (_≟_ to _≟-Meta_)
open import Reflection.TypeChecking.MonadSyntax public
  using (_<*>_; _<$>_; _>>=_)
open import Reflection.Term public
  using (Term)
open import Reflection.Pattern public
  using ()
  renaming (_≟_ to _≟-Pattern_)

open Sort public
open Pattern public
open Clause public

open import Category.Applicative
open import Category.Monad

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _++_; _==_)
open import Data.Float using (_==_)
open import Data.Char using (_==_)

open import Tools.List
open import Tools.Nat
open import Tools.Bool
open import Tools.Nullary
open import Tools.Product
open import Tools.Unit
open import Tools.Function

instance
  applicativeTC : ∀ {ℓ} → RawApplicative {ℓ} TC
  applicativeTC = record
    { pure = return
    ; _⊛_ = _<*>_
    }

instance
  monadTC : ∀ {ℓ} → RawMonad {ℓ} TC
  monadTC = record
    { return = return
    ; _>>=_ = _>>=_
    }

import Data.List.Categorical
open module ListTCA {ℓ} = Data.List.Categorical.TraversableA {ℓ} applicativeTC public
open module ListTCM {ℓ} = Data.List.Categorical.TraversableM {ℓ} monadTC public

-- Equality, weakening and strengthening from http://www.cse.chalmers.se/~nad/listings/equality/TC-monad.html

mutual
  -- Checks if the terms are syntactically equal.
  --
  -- Pattern-matching lambdas and "unknown" are currently never seen
  -- as equal to anything.
  --
  -- Note that this function does not perform any kind of parameter
  -- reconstruction.

  eq-Term : ATerm → ATerm → Bool
  eq-Term (var x₁ ts₁)   (var x₂ ts₂)   = Tools.Nat._==_ x₁ x₂ ∧ eq-Args ts₁ ts₂
  eq-Term (con c₁ ts₁)   (con c₂ ts₂)   = eq-Name c₁ c₂ ∧ eq-Args ts₁ ts₂
  eq-Term (def f₁ ts₁)   (def f₂ ts₂)   = eq-Name f₁ f₂ ∧ eq-Args ts₁ ts₂
  eq-Term (lam v₁ t₁)    (lam v₂ t₂)    = eq-Visibility v₁ v₂ ∧ eq-Abs t₁ t₂
  eq-Term (pi a₁ b₁)     (pi a₂ b₂)     = eq-Arg a₁ a₁ ∧ eq-Abs b₁ b₂
  eq-Term (agda-sort s₁) (agda-sort s₂) = eq-Sort s₁ s₂
  eq-Term (lit l₁)       (lit l₂)       = eq-Literal l₁ l₂
  eq-Term (meta x₁ ts₁)  (meta x₂ ts₂)  = eq-Meta x₁ x₂ ∧ eq-Args ts₁ ts₂
  eq-Term _              _              = false

  eq-Name : Name → Name → Bool
  eq-Name x₁ x₂ = isYes (x₁ ≟-Name x₂)

  eq-Meta : Meta → Meta → Bool
  eq-Meta x₁ x₂ = isYes (x₁ ≟-Meta x₂)

  eq-Sort : Sort → Sort → Bool
  eq-Sort (set t₁) (set t₂) = eq-Term t₁ t₂
  eq-Sort (lit n₁) (lit n₂) = Tools.Nat._==_ n₁ n₂
  eq-Sort _        _        = false

  eq-Literal : Literal → Literal → Bool
  eq-Literal (nat n₁)    (nat n₂)    = Tools.Nat._==_ n₁ n₂
  eq-Literal (float x₁)  (float x₂)  = Data.Float._==_ x₁ x₂
  eq-Literal (char c₁)   (char c₂)   = Data.Char._==_ c₁ c₂
  eq-Literal (string s₁) (string s₂) = Data.String._==_ s₁ s₂
  eq-Literal (name x₁)   (name x₂)   = eq-Name x₁ x₂
  eq-Literal (meta x₁)   (meta x₂)   = eq-Meta x₁ x₂
  eq-Literal _           _           = false

  eq-Args : List (Arg ATerm) → List (Arg ATerm) → Bool
  eq-Args []         []         = true
  eq-Args (t₁ ∷ ts₁) (t₂ ∷ ts₂) = eq-Arg t₁ t₂ ∧ eq-Args ts₁ ts₂
  eq-Args _          _          = false

  eq-Abs : Abs ATerm → Abs ATerm → Bool
  eq-Abs (abs s₁ t₁) (abs s₂ t₂) =
    Data.String._==_ s₁ s₂ ∧ eq-Term t₁ t₂

  eq-ArgInfo : ArgInfo → ArgInfo → Bool
  eq-ArgInfo (arg-info v₁ r₁) (arg-info v₂ r₂) =
    eq-Visibility v₁ v₂ ∧ eq-Relevance r₁ r₂

  eq-ArgX : Arg ATerm → Arg ATerm → Bool
  eq-ArgX (arg _ t₁) (arg _ t₂) = eq-Term t₁ t₂

  eq-Arg : Arg ATerm → Arg ATerm → Bool
  eq-Arg (arg i₁ t₁) (arg i₂ t₂) =
    eq-ArgInfo i₁ i₂ ∧ eq-Term t₁ t₂

  eq-Visibility : Visibility → Visibility → Bool
  eq-Visibility visible   visible   = true
  eq-Visibility hidden    hidden    = true
  eq-Visibility instance′ instance′ = true
  eq-Visibility _         _         = false

  eq-Relevance : Relevance → Relevance → Bool
  eq-Relevance relevant   relevant   = true
  eq-Relevance irrelevant irrelevant = true
  eq-Relevance _          _          = false

mutual
  -- The number of variables bound in the pattern(s).

  bound-in-pattern : Pattern → Nat
  bound-in-pattern (con _ ps) = bound-in-patterns ps
  bound-in-pattern dot        = 0
  bound-in-pattern (var _)    = 1
  bound-in-pattern (lit _)    = 0
  bound-in-pattern (proj _)   = 0
  bound-in-pattern absurd     = 0

  bound-in-patterns : List (Arg Pattern) → Nat
  bound-in-patterns []             = 0
  bound-in-patterns (arg _ p ∷ ps) =
    bound-in-pattern p + bound-in-patterns ps

mutual
  -- Weakening: weaken-term from by increases variables "from" and
  -- higher by "by".

  weaken-term : Nat → Nat → ATerm → ATerm
  weaken-term from by = λ where
    (var x args)      → var (weaken-var from by x)
                            (weaken-args from by args)
    (con c args)      → con c (weaken-args from by args)
    (def f args)      → def f (weaken-args from by args)
    (lam v t)         → lam v (weaken-abs from by t)
    (pat-lam cs args) → pat-lam (weaken-clauses from by cs)
                                (weaken-args from by args)
    (pi a b)          → pi (weaken-arg from by a) (weaken-abs from by b)
    (agda-sort s)     → agda-sort (weaken-sort from by s)
    (lit l)           → lit l
    (meta x args)     → meta x (weaken-args from by args)
    unknown           → unknown

  weaken-var : Nat → Nat → Nat → Nat
  weaken-var from by x = if isYes (from ≤? x) then x + by else x

  weaken-abs : Nat → Nat → Abs ATerm → Abs ATerm
  weaken-abs from by (abs s t) =
    abs s (weaken-term (Nat.suc from) by t)

  weaken-arg : Nat → Nat → Arg ATerm → Arg ATerm
  weaken-arg from by (arg i t) = arg i (weaken-term from by t)

  weaken-args : Nat → Nat → List (Arg ATerm) → List (Arg ATerm)
  weaken-args from by = λ where
    []       → []
    (a ∷ as) → weaken-arg from by a ∷ weaken-args from by as

  weaken-sort : Nat → Nat → Sort → Sort
  weaken-sort from by = λ where
    (set t) → set (weaken-term from by t)
    (lit n) → lit n
    unknown → unknown

  weaken-clause : Nat → Nat → Clause → Clause
  weaken-clause from by = λ where
    c@(absurd-clause _) → c
    (clause ps t)       →
      clause ps (weaken-term (bound-in-patterns ps + from) by t)

  weaken-clauses : Nat → Nat → List Clause → List Clause
  weaken-clauses from by = λ where
    []       → []
    (c ∷ cs) → weaken-clause from by c ∷ weaken-clauses from by cs

mutual
  -- Strengthening: strengthen-term from by subtracts "by" from
  -- variables "from" and higher. Applications of variable x, where
  -- from ≤ x and x < from + by, are replaced by "unknown".

  strengthen-term : Nat → Nat → Term → Term
  strengthen-term from by = λ where
    (var x args)      → let args′ = strengthen-args from by args in
                        if isYes (from + by ≤? x)
                        then var (x ∸ by) args′
                        else if isYes (from ≤? x)
                        then unknown
                        else var x args′
    (con c args)      → con c (strengthen-args from by args)
    (def f args)      → def f (strengthen-args from by args)
    (lam v t)         → lam v (strengthen-abs from by t)
    (pat-lam cs args) → pat-lam (strengthen-clauses from by cs)
                                (strengthen-args from by args)
    (pi a b)          → pi (strengthen-arg from by a)
                           (strengthen-abs from by b)
    (agda-sort s)     → agda-sort (strengthen-sort from by s)
    (lit l)           → lit l
    (meta x args)     → meta x (strengthen-args from by args)
    unknown           → unknown

  strengthen-abs : Nat → Nat → Abs Term → Abs Term
  strengthen-abs from by (abs s t) =
    abs s (strengthen-term (Nat.suc from) by t)

  strengthen-arg : Nat → Nat → Arg Term → Arg Term
  strengthen-arg from by (arg i t) = arg i (strengthen-term from by t)

  strengthen-args : Nat → Nat → List (Arg Term) → List (Arg Term)
  strengthen-args from by = λ where
    []       → []
    (a ∷ as) → strengthen-arg from by a ∷ strengthen-args from by as

  strengthen-sort : Nat → Nat → Sort → Sort
  strengthen-sort from by = λ where
    (set t) → set (strengthen-term from by t)
    (lit n) → lit n
    unknown → unknown

  strengthen-clause : Nat → Nat → Clause → Clause
  strengthen-clause from by = λ where
    c@(absurd-clause _) → c
    (clause ps t)       →
      clause ps (strengthen-term (bound-in-patterns ps + from) by t)

  strengthen-clauses : Nat → Nat → List Clause → List Clause
  strengthen-clauses from by = λ where
    []       → []
    (c ∷ cs) →
      strengthen-clause from by c ∷ strengthen-clauses from by cs

-- My utilities

argX : Arg ATerm → ATerm
argX (arg i x) = x

-- Returns the list of types in context without their arg-info,
-- but paired with their debrujin indices, s.t. the types are
-- all valid in the current context.
getContext' : TC (List (Nat × ATerm))
getContext' = do
  ctx ← getContext
  return (L.map
    (λ { (i , tp) → (i , weaken-term 0 (1 + i) (argX tp)) })
    (L.zip (L.upTo (L.length ctx)) ctx))

mapMaybeM : ∀ {a b} {A : Set a} {B : Set b} →
            (A → TC (Maybe B)) → List A → TC (List B)
mapMaybeM p []       = return []
mapMaybeM p (x ∷ xs) = do
  just y ← p x where
    nothing → mapMaybeM p xs
  _∷_ y <$> mapMaybeM p xs

-- Given a function which matches on the type of a term in the context
-- and maybe returns some stuff, returns a list of units of stuff.
filterCtx : ∀ {ℓ} {A : Set ℓ} → (Nat × ATerm → Maybe A) → TC (List A)
filterCtx flt = L.mapMaybe flt <$> getContext'

filterCtxM : ∀ {ℓ} {A : Set ℓ} → (Nat × ATerm → TC (Maybe A)) → TC (List A)
filterCtxM flt = getContext' >>= mapMaybeM flt

fmtTerms : List ATerm → List ErrorPart
fmtTerms = L.reverse ∘ᶠ L.foldl (λ lst tm → termErr tm ∷ lst) []

fmtArgs : List (Arg ATerm) → List ErrorPart
fmtArgs as = fmtTerms (L.map argX as)

dbg = debugPrint "woj" 2

-- Dumps the variables in context.
dumpCtx : TC ⊤
dumpCtx = do
  dbg (strErr "Context:" ∷ [])
  ctx ← getContext'
  mapM (λ { (i , tm) → do
    dbg (
      strErr ("[" ++ (show i) ++ "]")
      ∷ termErr tm
      ∷ []) }) ctx
  return tt

macro
  dumpCtxTac : Term → TC ⊤
  dumpCtxTac _ = dumpCtx
