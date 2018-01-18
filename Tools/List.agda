{-# OPTIONS --without-K --safe #-}

module Tools.List where

infixr 30 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
