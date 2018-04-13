
module IMP where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List

open import Util
open import Data

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
data Prog : Set where
  skip : Prog
  assign : (v : VName) → (e : AExp) → Prog
  semi : (c₁ c₂ : Prog) → Prog
  cond : (b : BExp) → (c₁ c₂ : Prog) → Prog
  while : (b : BExp) → (c : Prog) → Prog

-- some syntactic sugar
infixl 18 _:=_
pattern _:=_ v e = assign v e

infixl 15 _>>_
pattern _>>_ f g =  semi f g

pattern [IF_THEN_ELSE_FI] b c₁ c₂ = cond b c₁ c₂
pattern [WHILE_DO_OD] b c = while b c



-- An evaluation function for IMP
-- Takes an initial state to a colist of the state steps
eval : State → List Prog → CoList (State × Prog)
CoList.force (eval σ []) = inl <>
CoList.force (eval σ (skip ∷ cs))          = inr ((σ , skip) , eval σ cs)
CoList.force (eval σ (c'@(v := e) ∷ cs))   = inr ((σ , c') , eval (σ [ v ↦ e σ ]) cs)
CoList.force (eval σ (c'@(c₁ >> c₂) ∷ cs)) = inr ((σ , c') , eval σ (c₁ ∷ c₂ ∷ cs))
CoList.force (eval σ ([IF b THEN c₁ ELSE c₂ FI] ∷ cs)) with b σ
CoList.force (eval σ (c'@(cond b c₁ c₂) ∷ cs)) | false = inr ((σ , c') , eval σ (c₂ ∷ cs))
CoList.force (eval σ (c'@(cond b c₁ c₂) ∷ cs)) | true  = inr ((σ , c') , eval σ (c₁ ∷ cs))
CoList.force (eval σ ([WHILE b DO c OD] ∷ cs)) with b σ
CoList.force (eval σ (c'@(while b c) ∷ cs)) | false = inr ((σ , c') , eval σ cs)
CoList.force (eval σ (c'@(while b c) ∷ cs)) | true  = inr ((σ , c') , eval σ (c ∷ [WHILE b DO c OD] ∷ cs))
