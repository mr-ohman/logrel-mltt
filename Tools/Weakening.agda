{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Tools.Weakening where

open import Agda.Builtin.Strict
open import Agda.Builtin.String
open import Tools.List
open import Tools.Nat
open import Data.Nat using (_≤?_; _+_; _∸_; suc)
open import Tools.Reflection
open import Tools.Product
open import Tools.Nullary

