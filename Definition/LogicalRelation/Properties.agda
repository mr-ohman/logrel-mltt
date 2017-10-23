{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties {{eqrel : EqRelSet}} where


open import Definition.LogicalRelation.Properties.Reflexivity public
open import Definition.LogicalRelation.Properties.Symmetry public
open import Definition.LogicalRelation.Properties.Transitivity public
open import Definition.LogicalRelation.Properties.Conversion public
open import Definition.LogicalRelation.Properties.Escape public
open import Definition.LogicalRelation.Properties.Universe public
open import Definition.LogicalRelation.Properties.Neutral public
open import Definition.LogicalRelation.Properties.Reduction public
open import Definition.LogicalRelation.Properties.Successor public
open import Definition.LogicalRelation.Properties.MaybeEmb public
