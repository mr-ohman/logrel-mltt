{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions {{eqrel : EqRelSet}} where

open import Definition.LogicalRelation.Substitution.Introductions.Pi public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda public
open import Definition.LogicalRelation.Substitution.Introductions.Application public
open import Definition.LogicalRelation.Substitution.Introductions.Prod public
open import Definition.LogicalRelation.Substitution.Introductions.Fst public
open import Definition.LogicalRelation.Substitution.Introductions.Snd public
open import Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta public
open import Definition.LogicalRelation.Substitution.Introductions.Nat public
open import Definition.LogicalRelation.Substitution.Introductions.Natrec public
open import Definition.LogicalRelation.Substitution.Introductions.Empty public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec public
open import Definition.LogicalRelation.Substitution.Introductions.Unit public
open import Definition.LogicalRelation.Substitution.Introductions.Universe public
