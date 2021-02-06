{-# OPTIONS --without-K --safe #-}

module Tools.Fin where

open import Data.Fin public using (Fin ; fromℕ) renaming (zero to x0 ; suc to _+1)
