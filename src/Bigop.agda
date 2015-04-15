{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Bigop where

open import Bigop.Core public
open import Bigop.Ordinals public
open import Bigop.Filter public
open import Bigop.Filter.Predicates public

module Props where

  import Bigop.Ordinals.Properties as O
  module Ordinals = O

  import Bigop.Properties.Monoid as M
  module Monoid = M

  import Bigop.Properties.CommutativeMonoid as CM
  module CommutativeMonoid = CM

  import Bigop.Properties.SemiringWithoutOne as S-1
  module SemiringWithoutOne = S-1
