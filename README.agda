{-# OPTIONS --without-K --safe #-}

module README where

-- Formalization for "Decidability of Conversion for Type Theory in Type Theory"
-- Git repository: https://github.com/mr-ohman/logrel-mltt


------------------
-- INTRODUCTION --
------------------

-- A minimal library necessary for formalization:

-- The empty type and its elimination rule.
import Tools.Empty

-- The unit type.
import Tools.Unit

-- Sum type.
import Tools.Sum

-- Product type.
import Tools.Product

-- Identity function and composition.
import Tools.Function

-- Negation and decidability type.
import Tools.Nullary

-- Propositional equality and its properties.
import Tools.PropositionalEquality

-- Natural numbers and decidability of equality.
import Tools.Nat


---------------------------
-- LANGUAGE INTRODUCTION --
---------------------------

-- Syntax and semantics of weakening and substitution.
import Definition.Untyped

-- Propositional equality properties: Equalities between expressions,
-- weakenings, substitutions and their combined composition.
-- (These lemmas are not in the paper.)
import Definition.Untyped.Properties

-- Judgements: Typing rules, conversion, reduction rules
-- and well-formed substitutions and respective equality.
import Definition.Typed

-- Well-formed context extraction and reduction properties.
import Definition.Typed.Properties

-- Well-formed weakening and its properties.
import Definition.Typed.Weakening


------------------------------
-- KRIPKE LOGICAL RELATIONS --
------------------------------

-- Generic equality relation definition.
import Definition.Typed.EqualityRelation

-- The judgemental instance of the generic equality.
import Definition.Typed.EqRelInstance

-- Logical relations definitions.
import Definition.LogicalRelation

-- Properties of logical relation:

-- Reflexivity of the logical relation.
import Definition.LogicalRelation.Properties.Reflexivity

-- Escape lemma for the logical relation.
import Definition.LogicalRelation.Properties.Escape

-- Shape view of two or more types.
import Definition.LogicalRelation.ShapeView

-- Proof irrelevance for the logical relation.
import Definition.LogicalRelation.Irrelevance

-- Weakening of logical relation judgements.
import Definition.LogicalRelation.Weakening

-- Conversion of the logical relation.
import Definition.LogicalRelation.Properties.Conversion

-- Symmetry of the logical relation.
import Definition.LogicalRelation.Properties.Symmetry

-- Transitvity of the logical relation.
import Definition.LogicalRelation.Properties.Transitivity

-- Neutral introduction in the logical relation.
import Definition.LogicalRelation.Properties.Neutral

-- Weak head expansion of the logical relation.
import Definition.LogicalRelation.Properties.Reduction

-- Application in the logical relation.
import Definition.LogicalRelation.Application

-- Validity judgements definitions
import Definition.LogicalRelation.Substitution

-- Properties of validity judgements:

-- Proof irrelevance for the validity judgements.
import Definition.LogicalRelation.Substitution.Irrelevance

-- Properties about valid substitutions:
-- * Substitution well-formedness.
-- * Substitution weakening.
-- * Substitution lifting.
-- * Identity substitution.
-- * Reflexivity, symmetry and transitivity of substitution equality.
import Definition.LogicalRelation.Substitution.Properties

-- Single term substitution of validity judgements.
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

-- The fundamental theorem.
import Definition.LogicalRelation.Fundamental

-- Certain cases of the logical relation:

-- Validity of Π-types.
import Definition.LogicalRelation.Substitution.Introductions.Pi

-- Validity of applications.
import Definition.LogicalRelation.Substitution.Introductions.Application

-- Validity of λ-terms.
import Definition.LogicalRelation.Substitution.Introductions.Lambda

-- Validity of natural recursion of natural numbers.
import Definition.LogicalRelation.Substitution.Introductions.Natrec


-- Reducibility of well-formedness.
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the fundamental theorem:

-- Canonicity of the system.
import Definition.Typed.Consequences.Canonicity

-- Injectivity of Π-types.
import Definition.Typed.Consequences.Injectivity

-- Syntactic validitiy of the system.
import Definition.Typed.Consequences.Syntactic

-- All types and terms fully reduce to WHNF.
import Definition.Typed.Consequences.Reduction

-- Strong equality of types.
import Definition.Typed.Consequences.Equality

-- Syntactic inequality of types.
import Definition.Typed.Consequences.Inequality

-- Substiution in judgements and substitution composition.
import Definition.Typed.Consequences.Substitution

-- Uniqueness of the types of neutral terms.
import Definition.Typed.Consequences.NeTypeEq

-- Universe membership of types.
import Definition.Typed.Consequences.InverseUniv

-- Consistency of the type theory.
import Definition.Typed.Consequences.Consistency


------------------
-- DECIDABILITY --
------------------

-- Conversion algorithm definition.
import Definition.Conversion

-- Properties of conversion algorithm:

-- Context equality and its properties:
-- * Context conversion of typing judgements.
-- * Context conversion of reductions and algorithmic equality.
-- * Reflexivity and symmetry of context equality.
import Definition.Conversion.Stability

-- Soundness of the conversion algorithm.
import Definition.Conversion.Soundness

-- Conversion property of algorithmic equality.
import Definition.Conversion.Conversion

-- Decidability of the conversion algorithm.
import Definition.Conversion.Decidable

-- Symmetry of the conversion algorithm.
import Definition.Conversion.Symmetry

-- Transitivity of the conversion algorithm.
import Definition.Conversion.Transitivity

-- Weakening of the conversion algorithm.
import Definition.Conversion.Weakening

-- WHNF and neutral lifting of the conversion algorithm.
import Definition.Conversion.Lift

-- Generic equality relation instance for the conversion algorithm.
import Definition.Conversion.EqRelInstance

-- Completeness of conversion algorithm.
import Definition.Conversion.Consequences.Completeness

-- Decidability of judgemental conversion.
import Definition.Typed.Decidable
