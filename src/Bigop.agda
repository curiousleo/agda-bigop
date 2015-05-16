{-# OPTIONS --without-K #-}
-- see https://code.google.com/p/agda/issues/detail?id=1381

module Bigop where

open import Bigop.Core public
open import Bigop.Filter public
open import Bigop.Filter.Predicates public

module Props where

  module Ordinals where
    import Bigop.Ordinals.Properties.Nat as N
    module Nat = N
    import Bigop.Ordinals.Properties.Fin as F
    module Fin = F

  import Bigop.Filter.Properties as F
  module Filter = F

  import Bigop.Properties.Monoid as M
  module Monoid = M

  import Bigop.Properties.CommutativeMonoid as CM
  module CommutativeMonoid = CM

  import Bigop.Properties.SemiringWithoutOne as S-1
  module SemiringWithoutOne = S-1
