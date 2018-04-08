
module Data where

open import Agda.Primitive
open import Agda.Builtin.Nat hiding (_+_)
open import Agda.Builtin.List

-- List things

List-map : ∀ {o} {a b : Set o} → (a → b) → List a → List b
List-map f [] = []
List-map f (a ∷ as) = f a ∷ List-map f as

-- Basic Datatypes

data Zero : Set where

¬_ : ∀ {a} → Set a → Set a
¬ A = A → Zero

record One : Set where
  constructor <>

-- Data

infixr 16 _,_

-- Dependant pairs
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 10 _×_
record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A + B
  inr : B → A + B

data Maybe {x} (X : Set x) : Set x where
  none : Maybe X
  some : X → Maybe X

Maybe-map : ∀ {o} {a b : Set o} → (a → b) → Maybe a → Maybe b
Maybe-map a→b none = none
Maybe-map a→b (some x) = some (a→b x)



record CoList {x} (X : Set x) : Set x where
  coinductive
  field
    force : One + (X × CoList X)

module CoListDefs {x} {X : Set x} where
  open CoList

  -- force the same thing, forever
  forever : X → CoList X
  force (forever x) = inr (x , forever x)

  -- try to pull n elements from the front of a colist
  take : Nat → CoList X → List X
  take zero cs = []
  take (suc n) cs with force cs
  take (suc n) cs | inl <> = []
  take (suc n) cs | inr (c , cs') = c ∷ take n cs'

  try-get : Nat → CoList X → Maybe X
  try-get i cs with force cs
  try-get i cs | inl <> = none
  try-get zero cs | inr (c , cs') = some c
  try-get (suc i) cs | inr (c , cs') = try-get i cs'
