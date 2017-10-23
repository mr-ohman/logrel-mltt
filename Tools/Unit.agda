-- The unit type; also used as proposition ``Truth''.

{-# OPTIONS --without-K --safe #-}

module Tools.Unit where

-- We reexport Agda's built-in unit type.

open import Agda.Builtin.Unit public using (⊤; tt)
