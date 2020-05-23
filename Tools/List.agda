{-# OPTIONS --without-K --safe #-}

module Tools.List where

open import Data.List public using (List; []; _∷_)

module L where
  open import Data.List public

--infixr 30 _∷_
--_∷_ : ∀ {A : Set} → A → List A → List A
--_∷_ = DL._∷_

--data List (A : Set) : Set where
--  [] : List A
--  _∷_ : A → List A → List A
