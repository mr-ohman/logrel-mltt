-- The unit type; also used as proposition ``Truth''.

{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Tools.Unit where

-- We reexport Agda's built-in unit type.

open import Agda.Builtin.Unit public using (⊤; tt)
