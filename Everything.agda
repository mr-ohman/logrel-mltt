-- A Logical Relation for Dependent Type Theory Formalized in Agda

module Everything where

import Tools.Empty
import Tools.Unit
import Tools.Nat
import Tools.Product
import Tools.PropositionalEquality
--import Tools.HeterogeneousEquality
import Tools.Context

import Definition.Untyped
import Definition.Untyped.Indexed
import Definition.Untyped.Properties

import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening

import Definition.EqualityRelation

import Definition.LogicalRelation
import Definition.LogicalRelation.Tactic
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties

import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Soundness
import Definition.LogicalRelation.Substitution.Introductions

import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Consequences.Canonicity
import Definition.LogicalRelation.Consequences.Injectivity
import Definition.LogicalRelation.Consequences.Syntactic
import Definition.LogicalRelation.Consequences.SingleSubst
import Definition.LogicalRelation.Consequences.Inversion
import Definition.LogicalRelation.Consequences.Inequality
import Definition.LogicalRelation.Consequences.Substitution
import Definition.LogicalRelation.Consequences.Equality
import Definition.LogicalRelation.Consequences.InverseUniv

import Definition.Conversion
import Definition.Conversion.Conversion
import Definition.Conversion.Lift
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Symmetry
import Definition.Conversion.Transitivity
import Definition.Conversion.Universe
import Definition.Conversion.Validity
import Definition.Conversion.Weakening
import Definition.Conversion.Whnf
--import Definition.Conversion.Decidable
