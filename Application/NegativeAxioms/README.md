Consistent negative axioms do not do not jeopardize canonicity
==============================================================

Conjectured in https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

> T. Coquand, N.A. Danielsson, M.H. Escardo, U. Norell and Chuangjie Xu.
> Negative consistent axioms can be postulated without loss of canonicity.
> 3-page note.

One proof suggestion: analyse normal forms.

We work in MLTT ΣΠUℕ⊥.

A negative type is given by the following grammar, closed under conversion:

    N ::= ⊥
        | Π A N
        | Σ N₁ N₂

A negative context `Γⁿ` consists of just negative types.

Negative types are closed under weakening and substitution.
Using the non-confusion properties of MLTT, we can show that `ℕ` is
not a negative type.

Neutrals `n` and normal forms `v` are given as follows:

    n ::= x
        | n v
        | πᵢ n
        | ⊥-elim C n
        | ℕ-elim C v₀ vₛ n

    v ::= n
        | λv
        | (v₁,v₂)
        | zero
        | suc v
        | Π V V' | Σ V V' | ⊥ | ℕ | U

Judgement `Γ ⊢ n ⇉ A` expresses that `n` is a neutral of type `A` in context `Γ`.
Likewise `Γ ⊢ v ⇇ A` shall express that `v` is a normal form.

We would like to prove this lemma:

Lemma: In a negative consistent context `Γⁿ`, a neutral `n` is of negative type.

We prove `C` negative by induction on `Γⁿ ⊢ n : C`:

  - Case: variable `x : C ∈ Γⁿ`.  By definition of negative context.

  - Case: application `Γⁿ ⊢ n u ⇉ C`.  By IH, `Γⁿ ⊢ n ⇉ Π A N`,
    so `C = N[u]` negative.

  - Case: projection: analogously.

  - Case: conversion: by induction hypothesis, using closure of negatives under conversion.

  - Case: `⊥-elim n`.  Then `n` is a proof of `⊥`, in contradition to consistency.

  - Case: `ℕ-elim C z s n`.  By IH, the type of `n` is negative, but
    `ℕ` is not, so this case is impossible.
□

Lemma: In a negative consistent context `Γⁿ`, normal natural numbers must be numerals.

By induction on `Γⁿ ⊢ v : A`, we prove that `v` is a numeral given `Γⁿ ⊢ A ≡ ℕ`.

  - Case `zero`: that's what we said!

  - Case `suc v`: by IH.

  - Case neutral:

    By the previous lemma we know that `A` is negative, in contradiction to
    `Γⁿ ⊢ A = ℕ`.

  - The other cases contradict the non-confusion properties, thus, are impossible.
□

Theorem: In a consistent negative context, each term of type `ℕ` reduces to a numeral.

Proof.  The normalization theorem states:

  If `Γ ⊢ t : A` then `Γ ⊢ t = v : A` with `Γ ⊢ v : A`.

So the theorem follows from the previous lemma by normalization. □


Proof/file history:

- 2021-05-07 Andreas Abel, first version, using bidirectional typing
- 2021-05-27 Andreas Abel, simplified version with closures of negative types under conversion
- 2021-08-11 Andreas Abel, README
