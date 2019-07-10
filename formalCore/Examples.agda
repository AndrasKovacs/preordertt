{-# OPTIONS --prop --rewriting --type-in-type #-}

module Examples where

open import Lib
open import CwF
open import Universes
open import Pi

polyIdT : Ty ∙
polyIdT = Π∙ Sets (Π (ElS (coe {!!} (q= {∙} Sets))) (ElS {!!}))
