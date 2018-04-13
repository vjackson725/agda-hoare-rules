
module IMP where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)

{-
  Representation of the IMP language
-}

-- Variable Names
VName : Set
VName = Nat

-- Execution State
-- A map from variable names to natural numbers
State : Set
State = VName → Nat

-- An Expression that evaluated to a Nat
AExp : Set
AExp = State → Nat

-- An expression that evaluates to a Bool
BExp : Set
BExp = State → Bool

-- Data-structure representing IMP language primitives
data Com : Set where
  skip : Com
  assign : (v : VName) → (e : AExp) → Com
  semi : (c₁ c₂ : Com) → Com
  cond : (b : BExp) → (c₁ c₂ : Com) → Com
  while : (b : BExp) → (c : Com) → Com

-- some syntactic sugar
infixl 18 _:=_
pattern _:=_ v e = assign v e

infixl 15 _>>_
pattern _>>_ f g =  semi f g

pattern [IF_THEN_ELSE_FI] b c₁ c₂ = cond b c₁ c₂
pattern [WHILE_DO_OD] b c = while b c
