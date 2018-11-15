{-# OPTIONS --cubical #-}
module Primitives where

-- basically taken from <https://github.com/Saizan/cubical-demo>

module Postulates where
  open import Agda.Primitive.Cubical public
  open import Agda.Builtin.Cubical.Path public

  Path = _≡_

open Postulates public renaming
  ( primIMin       to _∧_   ; primIMax       to _∨_  ; primINeg   to ~_
  ; isOneEmpty     to empty )

module Unsafe' (dummy : Set₁) = Postulates
unsafeComp = Unsafe'.primComp Set
unsafePOr  = Unsafe'.primPOr  Set
